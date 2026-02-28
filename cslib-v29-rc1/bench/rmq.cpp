#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstring>
#include <unistd.h>
#include <sys/mman.h>
#include <sys/stat.h>
using u64 = uint64_t;
using u32 = uint32_t;
using u16 = uint16_t;

static constexpr auto LUT1 = [] {
    std::array<std::array<char, 4>, 10000> res;
    for (int i = 0; i < 10000; ++i) {
        res[i][0] = '0' + i / 1000;
        res[i][1] = '0' + i / 100 % 10;
        res[i][2] = '0' + i / 10 % 10;
        res[i][3] = '0' + i % 10;
        if (i < 1000) res[i][0] = ' ';
        if (i < 100) res[i][1] = ' ';
        if (i < 10) res[i][2] = ' ';
    }
    return res;
}();

static constexpr auto LUT2 = [] {
    std::array<std::array<char, 4>, 10000> res;
    for (int i = 0; i < 10000; ++i) {
        res[i][0] = '0' + i / 1000;
        res[i][1] = '0' + i / 100 % 10;
        res[i][2] = '0' + i / 10 % 10;
        res[i][3] = '0' + i % 10;
    }
    return res;
}();

constexpr bool all_digit(u64 x) {
    x ^= 0x3030303030303030;
    x &= 0xf0f0f0f0f0f0f0f0;
    return !x;
}

constexpr bool all_digit(u32 x) {
    x ^= 0x30303030;
    x &= 0xf0f0f0f0;
    return !x;
}

int main() {
    // Read all of stdin into a buffer (works with pipes, not just files)
    size_t cap = 1 << 20, total = 0;
    char* I = (char*)malloc(cap);
    for (;;) {
        ssize_t r = read(0, I + total, cap - total);
        if (r <= 0) break;
        total += r;
        if (total == cap) { cap *= 2; I = (char*)realloc(I, cap); }
    }
    I[total] = 0; // null-terminate
    const auto ii = [&]() {
        int x{};
        union {
            char ch[8];
            u64 a;
            u32 b;
        };
        memcpy(ch, I, 8);
        if (all_digit(a)) {
            a ^= 0x3030303030303030;
            a = (a * 10 + (a >> 8)) & 0x00ff00ff00ff00ff;
            a = (a * 100 + (a >> 16)) & 0x0000ffff0000ffff;
            a = (a * 10000 + (a >> 32)) & 0x00000000ffffffff;
            x = a, I += 8;
        } else if (all_digit(b)) {
            b ^= 0x30303030;
            b = (b * 10 + (b >> 8)) & 0x00ff00ff;
            b = (b * 100 + (b >> 16)) & 0x0000ffff;
            x = b, I += 4;
        }
        for (; *I > 47; ++I) x = x * 10 + *I - 48;
        ++I;
        return x;
    };
    char bufO[1 << 19], *ptrO = bufO, *endO = bufO + sizeof(bufO);
    auto flush = [&]() {
        write(1, bufO, ptrO - bufO);
        ptrO = bufO;
    };
    const auto print1 = [&](u32 x) {
        if (x > 9)
            memcpy(ptrO, &LUT1[x], 4), ptrO += 4;
        else
            *ptrO = x + '0', ptrO++;
    };
    const auto print2 = [&](u32 x) { memcpy(ptrO, &LUT2[x], 4), ptrO += 4; };
    const auto oo = [&](u64 x) {
        if (endO - ptrO < 20) flush();
        if (x > 9999'9999'9999ULL) {
            print1(x / 10000'0000'0000ULL);
            print2((x / 1'0000'0000ULL) % 10000);
            print2((x / 10000) % 10000);
            print2(x % 10000);
        } else if (x > 9999'9999) {
            print1(x / 10000 / 10000);
            print2(x / 10000 % 10000);
            print2(x % 10000);
        } else if (x > 9999) {
            print1(x / 10000);
            print2(x % 10000);
        } else {
            print1(x);
        }
        *ptrO = '\n', ptrO++;
    };
    int n = ii();
    int q = ii();
    int m = n / 16 + 1;
    int len = std::bit_width((unsigned)m);
    int* val = new int[n];
    int* suf = new int[n];
    int* pre = new int[n];
    int** table = new int*[len];
    for (int i = 0; i < len; ++i) table[i] = new int[m];
    for (int min, i = 0; i < n; ++i) {
        int id = i & 15;
        int value = pre[i] = val[i] = ii();
        suf[i] = min = id ? std::min(min, value) : value;
        if (id == 15) table[0][i / 16] = suf[i];
    }
    for (int min, i = n - 2; i >= 0; --i) {
        int id = ~i & 15;
        int value = pre[i];
        pre[i] = min = id ? std::min(min, value) : value;
    }
    for (int i = 1; i < len; ++i) {
        for (int j = 0, k = 1 << (i - 1); k < m; ++j, ++k) {
            table[i][j] = std::min(table[i - 1][j], table[i - 1][k]);
        }
    }
    u64 checksum = 0;
    for (int i = 0; i < q; ++i) {
        int l = ii();
        int r = ii();
        int L = l / 16;
        int R = r / 16;
        int ans;
        if (L == R) {
            ans = val[l];
            for (int i = l + 1; i <= r; ++i) ans = std::min(ans, val[i]);
        } else if (L == R - 1) {
            int p = pre[l];
            int s = suf[r];
            ans = std::min(p, s);
        } else {
            int p = pre[l];
            int s = suf[r];
            ans = std::min(p, s);
            int k = std::bit_width((unsigned)(R - L - 1)) - 1;
            int a = table[k][L + 1];
            int b = table[k][R - (1 << k)];
            int tmp = std::min(a, b);
            ans = std::min(ans, tmp);
        }
        checksum += ans;
    }
    oo(checksum);
    flush();
}
