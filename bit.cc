template <class T> constexpr T __rotl(T x, int s) noexcept {
    constexpr auto _Nd = numeric_limits<T>::digits;
    const int r = s % _Nd;
    if (r == 0) return x;
    else if (r > 0) return (x << r) | (x >> ((_Nd - r) % _Nd));
    else return (x >> -r) | (x << ((_Nd + r) % _Nd)); // rotr(x, -r)
}
template <class T> constexpr T __rotr(T x, int s) noexcept {
    constexpr auto _Nd = numeric_limits<T>::digits;
    const int r = s % _Nd;
    if (r == 0) return x;
    else if (r > 0) return (x >> r) | (x << ((_Nd - r) % _Nd));
    else return (x << -r) | (x >> ((_Nd + r) % _Nd)); // rotl(x, -r)
}
template <class T> constexpr int __countl_zero(T x) noexcept {
    constexpr auto _Nd = numeric_limits<T>::digits;
    if (x == 0) return _Nd;
    constexpr auto _Nd_ull = numeric_limits<unsigned long long>::digits;
    constexpr auto _Nd_ul = numeric_limits<unsigned long>::digits;
    constexpr auto _Nd_u = numeric_limits<unsigned>::digits;
    if constexpr (_Nd <= _Nd_u) {
        constexpr int diff = _Nd_u - _Nd;
        return __builtin_clz(x) - diff;
    } else if constexpr (_Nd <= _Nd_ul) {
        constexpr int diff = _Nd_ul - _Nd;
        return __builtin_clzl(x) - diff;
    } else if constexpr (_Nd <= _Nd_ull) {
        constexpr int diff = _Nd_ull - _Nd;
        return __builtin_clzll(x) - diff;
    } else { //(_Nd > _Nd_ull)
        static_assert(_Nd <= (2 * _Nd_ull), "Maximum supported integer size is 128-bit");
        unsigned long long high = x >> _Nd_ull;
        if (high != 0) {
            constexpr int diff = (2 * _Nd_ull) - _Nd;
            return __builtin_clzll(high) - diff;
        }
        constexpr auto __max_ull = numeric_limits<unsigned long long>::max();
        unsigned long long __low = x & __max_ull;
        return (_Nd - _Nd_ull) + __builtin_clzll(__low);
    }
}
template <class T> constexpr int __countl_one(T x) noexcept {
    if (x == numeric_limits<T>::max()) return numeric_limits<T>::digits;
    return __countl_zero<T>((T)~x);
}

template <class T> constexpr int __countr_zero(T x) noexcept {
    constexpr auto _Nd = numeric_limits<T>::digits;
    if (x == 0) return _Nd;
    constexpr auto _Nd_ull = numeric_limits<unsigned long long>::digits;
    constexpr auto _Nd_ul = numeric_limits<unsigned long>::digits;
    constexpr auto _Nd_u = numeric_limits<unsigned>::digits;
    if constexpr (_Nd <= _Nd_u) return __builtin_ctz(x);
    else if constexpr (_Nd <= _Nd_ul) return __builtin_ctzl(x);
    else if constexpr (_Nd <= _Nd_ull) return __builtin_ctzll(x);
    else // (_Nd > _Nd_ull)
    {
        static_assert(_Nd <= (2 * _Nd_ull), "Maximum supported integer size is 128-bit");
        constexpr auto __max_ull = numeric_limits<unsigned long long>::max();
        unsigned long long __low = x & __max_ull;
        if (__low != 0) return __builtin_ctzll(__low);
        unsigned long long high = x >> _Nd_ull;
        return __builtin_ctzll(high) + _Nd_ull;
    }
}
template <class T> constexpr int __countr_one(T x) noexcept {
    if (x == numeric_limits<T>::max()) return numeric_limits<T>::digits;
    return __countr_zero((T)~x);
}
template <class T> constexpr int __popcount(T x) noexcept {
    constexpr auto _Nd = numeric_limits<T>::digits;
    if (x == 0) return 0;
    constexpr auto _Nd_ull = numeric_limits<unsigned long long>::digits;
    constexpr auto _Nd_ul = numeric_limits<unsigned long>::digits;
    constexpr auto _Nd_u = numeric_limits<unsigned>::digits;
    if constexpr (_Nd <= _Nd_u) return __builtin_popcount(x);
    else if constexpr (_Nd <= _Nd_ul) return __builtin_popcountl(x);
    else if constexpr (_Nd <= _Nd_ull) return __builtin_popcountll(x);
    else { // (_Nd > _Nd_ull)
        static_assert(_Nd <= (2 * _Nd_ull), "Maximum supported integer size is 128-bit");
        constexpr auto __max_ull = numeric_limits<unsigned long long>::max();
        unsigned long long __low = x & __max_ull;
        unsigned long long high = x >> _Nd_ull;
        return __builtin_popcountll(__low) + __builtin_popcountll(high);
    }
}
template <class T> constexpr bool __has_single_bit(T x) noexcept { return __popcount(x) == 1; }
template <class T> constexpr T __bit_ceil(T x) noexcept {
    constexpr auto _Nd = numeric_limits<T>::digits;
    if (x == 0 || x == 1) return 1;
    auto shift_exponent = _Nd - __countl_zero((T)(x - 1u));
    using __promoted_type = decltype(x << 1);
    if constexpr (!is_same<__promoted_type, T>::value) {
        const int __extra_exp = sizeof(__promoted_type) / sizeof(T) / 2;
        shift_exponent |= (shift_exponent & _Nd) << __extra_exp;
    }
    return (T)1u << shift_exponent;
}
template <class T> constexpr T __bit_floor(T x) noexcept {
    constexpr auto _Nd = numeric_limits<T>::digits;
    if (x == 0) return 0;
    return (T)1u << (_Nd - __countl_zero((T)(x >> 1)));
}
template <class T> constexpr T __bit_width(T x) noexcept {
    constexpr auto _Nd = numeric_limits<T>::digits;
    return _Nd - __countl_zero(x);
}
template <class T, class U = T> using bit_require = enable_if_t<is_integral_v<T> && is_unsigned_v<T>, U>;

//[bit.cast]
template <class To, class From>
enable_if_t<(sizeof(To) == sizeof(From)) && is_trivially_copyable<From>::value && is_trivial<To>::value, To>
bit_cast(const From &src) noexcept {
    To dst;
    memcpy(&dst, &src, sizeof(To));
    return dst;
}
// [bit.rot], rotating
/// Rotate `x` to the left by `s` bits.
template <class T> constexpr bit_require<T> rotl(T x, int s) noexcept { return __rotl(x, s); }
/// Rotate `x` to the right by `s` bits.
template <class T> constexpr bit_require<T> rotr(T x, int s) noexcept { return __rotr(x, s); }

// [bit.count], counting
/// The number of contiguous zero bits, starting from the highest bit.
template <class T> constexpr bit_require<T, int> countl_zero(T x) noexcept { return __countl_zero(x); }
/// The number of contiguous one bits, starting from the highest bit.
template <class T> constexpr bit_require<T, int> countl_one(T x) noexcept { return __countl_one(x); } 
/// The number of contiguous zero bits, starting from the lowest bit.
template <class T> constexpr bit_require<T, int> countr_zero(T x) noexcept { return __countr_zero(x); }
/// The number of contiguous one bits, starting from the lowest bit.
template <class T> constexpr bit_require<T, int> countr_one(T x) noexcept { return __countr_one(x); }
/// The number of bits set in `x`.
template <class T> constexpr bit_require<T, int> popcount(T x) noexcept { return __popcount(x); }

// [bit.pow.two], integral powers of 2
/// True if `x` is a power of two, false otherwise.
template <class T> constexpr bit_require<T, bool> has_single_bit(T x) noexcept { return __has_single_bit(x); }
/// The smallest power-of-two not less than `x`.
template <class T> constexpr bit_require<T> bit_ceil(T x) noexcept { return __bit_ceil(x); }
/// The largest power-of-two not greater than `x`.
template <class T> constexpr bit_require<T> bit_floor(T x) noexcept { return __bit_floor(x); }
/// The smallest integer greater than the base-2 logarithm of `x`.
template <class T> constexpr bit_require<T> bit_width(T x) noexcept { return __bit_width(x); }

/// Byte order
enum class endian {
    little = __ORDER_LITTLE_ENDIAN__,
    big = __ORDER_BIG_ENDIAN__,
    native = __BYTE_ORDER__
};

