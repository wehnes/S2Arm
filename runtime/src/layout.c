// Mac/iOS 共用的区域布局（docs/方案_地址空间根修.md）。只看 NPDM（地址空间类型、SystemResourceSize）、模块跨度和宿主占到的窗口，不看按款表。
// Horizon 各区是地址承诺，不是内存：游戏真占的只有它映射过的页。宿主占到的窗口放得下标准布局就照标准排（甲）；放不下就把必须有宿主地址的
//   小区（模块、栈、堆、共享映射余量、TLS/IO）排在窗口前段，只有「从低往高长」的别名区伸出窗口（乙）——伸出去的部分只是承诺，
//   游戏映射到那里时 svc 回内存不足（svc_mem.c win_has），不崩。
#include "native.h"
#include "as_type.h"
#include <errno.h>
#if defined(__IPHONE_OS_VERSION_MIN_REQUIRED)
#include <mach/mach.h>
#include <os/proc.h>
#endif

#define GB (1ull << 30)
#define MB (1ull << 20)
#define A2M(x) (((x) + 2 * MB - 1) & ~(2 * MB - 1))
#define AGB(x) (((x) + GB - 1) & ~(GB - 1))

// VAMM 别名区：Switch 39 位给 64 GiB，SDK 开头放元数据 0x3FE00000，≥1 GiB 的地址区按 GiB 对齐且前后留 4 KiB——
//   别名区基址 ≡ 2 MiB − 16 KiB（mod 1 GiB）、长 63 GiB + 32 KiB − 2 MiB 时，UE4 开局要的 62 GiB 正好放下（地址空间.md A11）
#define VAMM_ALIAS (63 * GB)
// 栈区照 Horizon 39 位给 2 GiB（Ryujinx KPageTableBase stackRegion.Size = 0x80000000）：SDK 建线程（StackGuardManager::MapAtRandomAddress）
//   在栈区里随机挑地址、前后各留保护区，512 次都撞上已占的就中止（Break 原因 0）。10-29 Servonauts / Fit Boxing 3 线程栈占到 43–51 MB 时
//   128 MiB 栈区挑不出位置、开局约 40 秒中止。只有别名优先的款仍压到 128 MiB（同堆一起给别名区让窗口：巫师3 碰到 49.1 GB，iOS 26 窗口 51 GB）
#define VAMM_STACK (2 * GB)
#define ALIAS_FIRST_STACK (128 * MB)
#define VAMM_SHARED (96 * MB)   // 共享内存 / 传输内存随机映射的余量（可随机区 = 栈 + 堆 + 余量）
#define MIN_HEAP (32 * MB)
#define ALIAS_FIRST_HEAP (192 * MB)   // 别名优先的乙布局：堆 64 MiB + 远端影子余量 128 MiB（影子与堆共用堆区）
// 窗口里留给宿主自己的地址（Metal 大缓冲、窗口尾部统一分配）：现行包里 63.25 GiB 的款在 64 GiB 空洞里留下的就是这么多（vawin.c TL_SMALL 注释：766 MB），
//   甲里堆先让出它（甲的窗口尾在别名区之外）。乙不在窗口里留：别名区伸出窗口，窗口尾还给宿主就和远端承诺段重叠——
//   宿主放进去的东西会被游戏的远端访问静默读写；乙的宿主保留段由 vawin.c 放在窗口下方
#define HOST_KEEP (768 * MB)

static void vamm_alias(s2a_layout *o, uint64_t t) {   // t：1 GiB 对齐的 TLS/IO 起点
    o->tlsio_base = t;                 o->tlsio_size = 2 * MB - 0x4000;
    o->alias_base = t + 2 * MB - 0x4000; o->alias_size = VAMM_ALIAS + 0x8000 - 2 * MB;
}
static void vamm_small(s2a_layout *o, uint64_t at, uint64_t stack, uint64_t heap) {   // 栈 → 堆 → 共享余量，可随机区罩住三者
    o->stack_base = at;                o->stack_size = stack;
    o->heap_base = at + stack;         o->heap_size = heap;
    o->aslr_base = at;                 o->aslr_size = stack + heap + VAMM_SHARED;
}
static uint64_t g_app_pool = 0xCD500000ull;
static pthread_once_t g_pool_once = PTHREAD_ONCE_INIT;
static uint64_t g_pool_cap = UINT64_MAX;

// Total process allowance, including allocations already made at startup.
// UINT64_MAX means unavailable. A measured zero is a valid exhausted limit.
// The weak provider lets host tests cover device limits without iOS hardware.
__attribute__((weak)) uint64_t s2a_app_pool_process_limit(void) {
#if defined(__IPHONE_OS_VERSION_MIN_REQUIRED)
    task_vm_info_data_t info; mach_msg_type_number_t count = TASK_VM_INFO_COUNT;
    uint64_t available = os_proc_available_memory();
    if (task_info(mach_task_self(), TASK_VM_INFO, (task_info_t)&info, &count) != KERN_SUCCESS || available > UINT64_MAX - info.phys_footprint)
        return UINT64_MAX;
    return available + info.phys_footprint;
#else
    return UINT64_MAX;
#endif
}

static int pool_mb(const char *value, uint64_t *bytes) {
    if (!value || *value < '0' || *value > '9') return -1;
    char *end; errno = 0;
    uint64_t mb = strtoull(value, &end, 10);
    if (errno || *end || mb > UINT64_MAX / MB) return -1;
    *bytes = mb * MB;
    return 0;
}

static void app_pool_config(void) {
    const char *value = getenv("S2A_APP_POOL_MB");
    if (!value || !*value) return;   // native capacity is the default
    g_pool_cap = 0;   // an invalid explicit experiment must fail before launch
    if (strcmp(value, "auto")) {
        uint64_t bytes;
        if (pool_mb(value, &bytes)) { LOG("【红】S2A_APP_POOL_MB 需为非负整数 MiB 或 auto，实验预算无效"); return; }
        g_pool_cap = bytes ? bytes : UINT64_MAX;   // 0 explicitly restores native
        if (bytes) LOG("实验应用池上限 %llu MiB（S2A_APP_POOL_MB，仍受本款原生池上限约束）", (unsigned long long)(bytes / MB));
        return;
    }
    uint64_t reserve = 2560 * MB;
    const char *setting = getenv("S2A_APP_POOL_RESERVE_MB");
    if (setting && *setting && pool_mb(setting, &reserve)) { LOG("【红】S2A_APP_POOL_RESERVE_MB 需为非负整数 MiB，实验预算无效"); return; }
    uint64_t limit = s2a_app_pool_process_limit();
    if (limit == UINT64_MAX) { LOG("【红】自动客体预算取不到 iOS 进程内存额度，请恢复原生预算或显式指定 MiB"); return; }
    if (limit <= reserve) { LOG("【红】自动客体预算无可用空间：进程额度 %llu MiB、预留 %llu MiB", (unsigned long long)(limit / MB), (unsigned long long)(reserve / MB)); return; }
    g_pool_cap = (limit - reserve) & ~(2 * MB - 1);
    LOG("实验自动应用池上限 %llu MiB：进程额度 %llu MiB、宿主与安全预留 %llu MiB（本进程固定，仍受原生池约束）",
        (unsigned long long)(g_pool_cap / MB), (unsigned long long)(limit / MB), (unsigned long long)(reserve / MB));
}

uint64_t s2a_app_pool(void) {
    pthread_once(&g_pool_once, app_pool_config);
    return g_app_pool < g_pool_cap ? g_app_pool : g_pool_cap;
}
void s2a_app_pool_set(uint64_t v) { g_app_pool = v; }
static void heapmode(s2a_layout *o, uint64_t b) {   // 堆模式（系统资源为 0）沿用 39 位布局；物理分配仍受应用池限制。别名区不调 MapPhysicalMemory 就不碰
    // 堆区 6 GiB；应用池比它大（Switch 2 的 9 GiB）时堆区放大到池（GiB 对齐），否则 SetHeapSize 给不满池（Pokopia 开局要约 8 GiB 堆）。别名区顺延，32 GiB 跨度内放得下
    uint64_t heap = AGB(S2A_APP_POOL) > 6 * GB ? AGB(S2A_APP_POOL) : 6 * GB;
    o->tlsio_base = b;          o->tlsio_size = GB;
    o->stack_base = b + GB;     o->stack_size = 2 * GB;
    o->heap_base = b + 3 * GB;  o->heap_size = heap;
    o->alias_base = b + 3 * GB + heap; o->alias_size = 8 * GB;
    o->aslr_base = b;           o->aslr_size = 32 * GB;
}

// 36 位（NPDM 地址空间类型 1，老 SDK）照 Ryujinx KPageTableBase AddressSpace64BitDeprecated：代码区 0x78000000，栈区与 TLS/IO 区不单列、
//   就是代码区（stackAndTlsIo = 代码区），堆区 6 GiB（同 heapmode：应用池更大时放大到池）、别名区 0x180000000，可随机区罩住全部（Ryujinx 是整个 2^36，
//   这里同堆模式给 32 GiB，其余 18 GiB 留给共享内存 / 传输内存随机映射）。各区都要在 2^36 以下：老 SDK 打包 HIPC 缓冲描述符只编 36 位地址
//   （sdk HipcMessageBufferAccessor::SetSend 只取地址 32–35 位，36–38 位不写），游戏地址落在 2^36 以上传给服务就丢了高位（s2a_as_type_top）。
//   代码区 [W, W + 0x78000000) 里依次是模块段、TLS/IO（TLR 页，不进 GetInfo）、栈区：报给游戏的栈区去掉前两段（Ryujinx 的栈区 = 整个代码区，
//   内核在区里找空位；我方 MapMemory 只核映射表、TLR 按序往上切，栈区与模块 / TLR 重叠就会被映射盖掉，同 39 位各区不相交的做法）。主线程栈照旧在栈区最高处
#define AS36_CODE 0x78000000ull
#define AS36_ALIAS 0x180000000ull
#define AS36_TLR (2 * MB)
static uint64_t as36_heap(void) { return AGB(S2A_APP_POOL) > 6 * GB ? AGB(S2A_APP_POOL) : 6 * GB; }
static int as36(s2a_layout *o, uint64_t W, uint64_t S, uint64_t mod, uint64_t *mod_base) {
    uint64_t heap = as36_heap(), span = AGB(AS36_CODE) + heap + AS36_ALIAS;   // 代码区 → 堆 → 别名：最少要这么多宿主地址
    if (mod + AS36_TLR >= AS36_CODE || S < span) return -2;   // 模块 + TLR 要在代码区里给栈留地方
    uint64_t asz = S >= 32 * GB ? 32 * GB : S & ~(GB - 1);
    o->tlsio_base = W + mod;               o->tlsio_size = AS36_TLR;
    o->stack_base = W + mod + AS36_TLR;    o->stack_size = AS36_CODE - mod - AS36_TLR;
    o->heap_base = W + AGB(AS36_CODE);     o->heap_size = heap;
    o->alias_base = o->heap_base + heap;   o->alias_size = AS36_ALIAS;
    o->aslr_base = W;                      o->aslr_size = asz;
    *mod_base = W; o->win_size = asz;
    return 0;
}

// 甲（标准）布局的跨度：VAMM = 别名 + 小区（堆给满应用池）+ 模块；堆模式 = 32 GiB + 模块。宿主占窗口按它要（vawin.c），要不到整块也照样起
uint64_t s2a_layout_need(uint32_t as_type, uint64_t sys_resource_size, uint64_t module_span) {
    if (S2A_APP_POOL <= sys_resource_size) return 0;
    if ((as_type != 3 && as_type != 1) || module_span > 64 * GB) return 0;
    uint64_t mod = A2M(module_span);
    if (as_type == 1) return mod + AS36_TLR >= AS36_CODE ? 0 : 32 * GB;   // 模块在代码区里，跨度就是可随机区
    return sys_resource_size ? VAMM_ALIAS + 2 * MB + VAMM_STACK + S2A_HEAP_DEFAULT + VAMM_SHARED + mod : 32 * GB + mod;
}

int s2a_layout_compute(uint32_t as_type, uint64_t sys_resource_size, uint64_t module_span, int alias_gb, uint64_t W, uint64_t S, s2a_layout *o, uint64_t *mod_base, uint64_t *shadow_base) {
    memset(o, 0, sizeof *o); *mod_base = *shadow_base = 0;
    if (S2A_APP_POOL <= sys_resource_size) {
        LOG("【红】客体应用池预算不足或配置无效：池 %llu MiB、NPDM 系统资源 %llu MiB", (unsigned long long)(S2A_APP_POOL / MB), (unsigned long long)(sys_resource_size / MB));
        return -3;
    }
    uint64_t top = s2a_as_type_top(as_type);
    if (!top) return -1;
    if ((W & (GB - 1)) || module_span > 64 * GB || W > top || S > top - W) return -2;
    uint64_t mod = A2M(module_span);
    o->win_base = W; o->as_type = as_type; o->sys_resource_size = sys_resource_size;
    if (as_type == 1) { if (as36(o, W, S, mod, mod_base)) { memset(o, 0, sizeof *o); return -2; } return 0; }
    if (sys_resource_size) {
        // 甲：别名区在前、整段有宿主地址；其后栈 / 堆 / 余量 / 模块。堆只对别名优先的款让位（从应用池上限往下让到窗口放得下，至少 32 MiB）——
        //   别的款不知道要多大堆（王国之泪首次就要 2.05 GB），放不下「别名 + 满额堆」就走乙：堆给满放前段、别名区伸出窗口（承诺，远端翻译兜底）
        uint64_t stack = alias_gb ? ALIAS_FIRST_STACK : VAMM_STACK, fixed = VAMM_ALIAS + 2 * MB + stack + VAMM_SHARED + mod;
        if (alias_gb ? S >= fixed + MIN_HEAP : S >= fixed + S2A_HEAP_DEFAULT) {
            uint64_t heap = S >= fixed + HOST_KEEP + MIN_HEAP ? (S - fixed - HOST_KEEP) & ~(2 * MB - 1) : MIN_HEAP;
            if (heap > S2A_HEAP_DEFAULT) heap = S2A_HEAP_DEFAULT;
            vamm_alias(o, W);
            vamm_small(o, W + VAMM_ALIAS + 2 * MB, stack, heap);
            *mod_base = o->aslr_base + o->aslr_size;
            o->win_size = fixed + heap;
            return 0;
        }
        // 乙：模块、栈、堆、余量在前段，别名区在其后、伸出窗口（伸出段的内容放影子区，far.c）。影子区与堆共用堆区这段地址：
        //   堆从底往上长、影子块从顶往下分——两者真占的物理页合起来受应用池封顶，地址不必各留一份（iOS 26 大空洞只有 51.0 GiB，省下的都给别名区）
        //   别名优先（出包静态认出「开局在别名区要一整块巨大地址区」= 内存走 VAMM 自管，tools/addr_need.py static_alias_gb）：堆区 64 MiB +
        //   影子余量 128 MiB，别名区紧接前段、不按 GiB 对齐，窗口里放不下要的时承诺放到 64 GiB（元数据 ≤1 GiB + 对齐浪费 ≤1 GiB + 62 GiB 照样放下，SDK 对齐没被削也成立）——
        //   巫师3 碰到 49.1 GB，iOS 26 的 [12, 63) GB 空洞（下方 1 GiB 留宿主）放得下的前提
        vamm_small(o, W + mod, stack, alias_gb ? ALIAS_FIRST_HEAP : S2A_HEAP_DEFAULT + S2A_FAR_SLACK);
        uint64_t t = alias_gb ? A2M(o->aslr_base + o->aslr_size) : AGB(o->aslr_base + o->aslr_size);
        if (t + 2 * MB > W + S) { memset(o, 0, sizeof *o); return -2; }   // 前段 + TLS/IO 都放不下
        vamm_alias(o, t);
        // 别名优先：承诺 = 宿主兜得住的那段（别名区收到窗口末、不开远端），前提是放得下游戏代码证明要的；放不下才承诺 64 GiB、伸出段走远端。
        //   SDK 给新地址区挑位置是「最高那段空隙的底部」（VammManager::AllocateAddressRegion 的找空隙函数从末尾哨兵往前走前驱，
        //   火炬之光3 sdk+0xd23d0 反汇编），活着的地址区一路往上爬：承诺多高、游戏迟早碰到多高，与真用多少无关——火炬之光3 真映射 1.2 GB，
        //   地址爬到 64 GiB 别名区顶 +63.4 GB，伸出窗口那 1.5 GB 一碰就缺页代执行，每帧约 150 ms。
        //   要的（11-03 维护者：账要算对，不选倍数）= 静态大区连元数据（alias_gb，addr_need.py 已含 0x3FE00000）+ 大区按 GiB 对齐最多浪费 1 GiB
        //   + 大区之外活着的地址区的最坏地址账：这些区都整段提交（上限不定的款不走这里），提交总量 ≤ 应用池 P；SDK 放区的起点
        //   = (前一区末 + (粒度 | 0xFFF)) & −粒度（sdk+0xd23d0），每个区最多多占「粒度 + 0xFFF」，粒度 <2 MiB 的区是 64 KiB、
        //   [2, 4) MiB 是 2 MiB、[4, 32) MiB 是 4 MiB、[32 MiB, 1 GiB) 是 32 MiB、≥1 GiB 是 1 GiB（地址空间.md A6）。
        //   每字节提交最坏占地址 = (4 KiB + 64 KiB + 0xFFF) / 4 KiB < 18（4 KiB 小区；≥2 MiB 的区不到 2.01）→ 18 P；末区之后再留 4 KiB 保护页
        //   出包读码判「上限不定」（alias_gb < 0：有只占地址、尺寸非常量的申请，addr_need.py alias_unbounded）：证明不了就不收，照旧 64 GiB + 远端（宁慢不崩）
        if (alias_gb) {
            uint64_t fit = W + S - o->alias_base, need = (uint64_t)(alias_gb < 0 ? -alias_gb : alias_gb) * GB + GB + 18 * S2A_APP_POOL + 0x2000;
            o->alias_size = alias_gb > 0 && fit >= need ? fit : 64 * GB;
        }
        *mod_base = W; *shadow_base = o->alias_base + o->alias_size > W + S ? o->heap_base : 0; o->win_size = S;
        return 0;
    }
    if (S >= 32 * GB + mod) { heapmode(o, W); *mod_base = W + 32 * GB; o->win_size = 32 * GB + mod; return 0; }
    // 乙：模块在前，各区整体后移到下一个 GiB；堆区之前的部分（TLS/IO、栈）与至少 32 MiB 堆必须有宿主地址
    uint64_t b = AGB(W + mod);
    heapmode(o, b);
    if (o->heap_base + MIN_HEAP > W + S) { memset(o, 0, sizeof *o); return -2; }
    *mod_base = W; o->win_size = S;
    return 0;
}
