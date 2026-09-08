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
