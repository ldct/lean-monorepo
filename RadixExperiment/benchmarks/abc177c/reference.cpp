// Radix batch runtime v1. This exact prelude is embedded in each submission.
#include <cstdio>
#include <cstdlib>
#include <limits>
#include <new>

using u64 = unsigned long long;
static_assert(std::numeric_limits<u64>::digits == 64);

[[noreturn]] void reject() { std::exit(EXIT_FAILURE); }

bool radix_space(int c) { return (c >= 9 && c <= 13) || c == 32; }

void read_u64(u64& destination) {
    int c = std::getchar();
    while (radix_space(c)) c = std::getchar();
    if (c < '0' || c > '9') reject();
    u64 value = 0ULL;
    do {
        u64 digit = static_cast<u64>(c - '0');
        if (value > (std::numeric_limits<u64>::max() - digit) / 10ULL) reject();
        value = value * 10ULL + digit;
        c = std::getchar();
    } while (c >= '0' && c <= '9');
    if (c != EOF && !radix_space(c)) reject();
    if (std::ferror(stdin)) reject();
    destination = value;
}

void write_u64(u64 value) {
    if (std::printf("%llu", value) < 0) reject();
}

template <std::size_t N> void write_text(const char (&text)[N]) {
    if (std::fwrite(text, 1, N - 1, stdout) != N - 1) reject();
}

void expect_eof() {
    int c = std::getchar();
    while (radix_space(c)) c = std::getchar();
    if (c != EOF || std::ferror(stdin)) reject();
}

void solve() {
    u64 n = 0ULL;
    read_u64(n);
    if (n < 2ULL || n > 200000ULL) { reject(); }
    u64* a = new u64[n]();
    u64 k = 0ULL;
    while (k < n) {
        u64 x = 0ULL;
        read_u64(x);
        if (x > 1000000000ULL) { reject(); }
        a[k] = x;
        k = k + 1ULL;
    }
    expect_eof();
    u64 m = 1000000007ULL;
    u64 answer = 0ULL;
    u64 j = 0ULL;
    while (j < n) {
        u64 i = 0ULL;
        while (i < j) {
            answer = (answer + a[i] * a[j]) % m;
            i = i + 1ULL;
        }
        j = j + 1ULL;
    }
    write_u64(answer);
    write_text("\n");
}

int main() { solve(); return 0; }
