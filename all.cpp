#include <bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
#define debug(...) cout << #__VA_ARGS__ << "\t" << forward_as_tuple(__VA_ARGS__)/ebra << endl;
#define ALL(...) begin(__VA_ARGS__), end(__VA_ARGS__)
#define RALL(...) rbegin(__VA_ARGS__), rend(__VA_ARGS__)
// [decompose.vector.size]
inline constexpr size_t vector_size_v = 2;

inline namespace my {
// [detail.macro]
#define FWD(...) static_cast<decltype(__VA_ARGS__)&&>(__VA_ARGS__)
#define concept inline constexpr bool
#define INLINE_BOOL inline constexpr bool    
using namespace std;
using ll = long long int;
using ull = unsigned long long int;

namespace pbdsdetail {
using namespace __gnu_pbds;
template<class T, class V = null_type, class C = less<>>
using order_tree = tree<T, V, C, rb_tree_tag, tree_order_statistics_node_update>;
} // namespace pbds
using pbdsdetail::order_tree;
template<int N>
constexpr auto SieveOfEuler_() {
    array<int, N + 1> prime {};
    array<bool, N + 1> notPrime {};
    int pos = 0;
    for (int i = 2; i != N + 1; ++i) {
        if (!notPrime[i]) prime[pos++] = i;
        for (int i = 0; i != pos; ++i) {
            auto p = prime[i];
            if (auto idx = 1l * p * i; idx <= N) {
                notPrime[idx] = 1;
                if (i % p == 0) break;
            }
        }
    }
    return pair {prime, pos};
};
inline namespace type_traits {

template<class T> struct type_identity { using type = T; };
template<class T> using type_identity_t = typename type_identity<T>::type;
    
template<class T, class... Args> concept is_any_of = ( is_same_v<T, Args> || ... );

template<class T, class = void> INLINE_BOOL is_tuple_like = false;

template<class T> INLINE_BOOL is_tuple_like<T, void_t<decltype(tuple_size<T> {})>> = true;
template<class T> concept tuple_like = is_tuple_like<remove_reference_t<T>>;    

}
inline namespace concepts {
    template<class T, class U> concept derived_from = is_base_of_v<U, T>;
    template<class T> concept movable = is_convertible_v<T, T>;//[[not precisely]]
}
inline namespace integer {
template<class T> constexpr make_unsigned_t<T> to_unsigned(T t) noexcept { return t; }
template<class T> constexpr make_signed_t<T> to_signed(T t) noexcept { return t; }

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
enum class endian { little = __ORDER_LITTLE_ENDIAN__, big = __ORDER_BIG_ENDIAN__, native = __BYTE_ORDER__ };

}
inline namespace algo {

struct identity { template<class T> T&& operator()(T&& t) const { return (T&&)t; }  };
template<class C = less<>, class P = identity>
struct proj_cmp {
    C comp;
    P proj;
    template<class CC, class PP> 
    proj_cmp(CC&& comp, PP&& proj) : comp((CC&&)comp), proj((PP&)proj) {}
    template<class T, class U> decltype(auto) operator()(T&& t, U&& u) const 
    { return invoke(comp, invoke(proj, (T&&)t), invoke(proj, (U&&)u)); }
};
template<class C, class P> proj_cmp(C, P)->proj_cmp<C, P>;

}

inline namespace ITER {
    template<class T> using iter_difference_t = ptrdiff_t;// [[todo]]
    template<class I> using iter_value_t = typename iterator_traits<I>::value_type;
    template<class T> using iter_reference_t = decltype(*declval<T>());
    template<class T> using iter_rvalue_reference_t = iter_reference_t<T>; // [[todo]] = decltype(ranges::iter_move(declval<T&>()));

    //[default.sentinel]
    struct default_sentinel_t {};
    inline constexpr default_sentinel_t default_sentinel {};

    //[unreachable.sentinel]
    struct unreachable_sentinel_t { //[[todo] : I is weakly_incrementable]
        template<class I> friend constexpr bool operator==(I, unreachable_sentinel_t) { return false; }
        template<class I> friend constexpr bool operator!=(I, unreachable_sentinel_t) { return true; }
        template<class I> friend constexpr bool operator==(unreachable_sentinel_t, I) { return false; }
        template<class I> friend constexpr bool operator!=(unreachable_sentinel_t, I) { return true; } 
    };
    inline constexpr unreachable_sentinel_t unreachable_sentinel {};
    
} // namespace ITER
namespace ranges {
//[ranges.range] concepts
template<class T, class = void> INLINE_BOOL range_impl = false;
template<class T> INLINE_BOOL range_impl<T, void_t<decltype(begin(declval<T&>()), end(declval<T&>()))>> = true;
template<class T> concept range = range_impl<T>;
    //[[todo] borrowed_range enable_borrowed_range]
template<class T> using iterator_t = decay_t<decltype(begin(declval<T&>()))>;
template<class T> using sentinel_t = decay_t<decltype(end(declval<T&>()))>;

template<class R> using range_size_t = decltype(/*ranges::*/size(declval<R&>()));
template<class R> using range_difference_t = iter_difference_t<iterator_t<R>>;
template<class R> using range_value_t = iter_value_t<iterator_t<R>>;
template<class R> using range_reference_t = iter_reference_t<iterator_t<R>>;
template<class R> using range_rvalue_reference_t = iter_rvalue_reference_t<iterator_t<R>>;

//[range.sized]s
template<class T, class=void> INLINE_BOOL sized_range_impl = false;
template<class T> INLINE_BOOL sized_range_impl<T, void_t<decltype(/*ranges::*/size(declval<T&>()))>> = range<T>;
template<class T> concept sized_range = sized_range_impl<T>;

//[range.view]
struct view_base { };
template<class T> struct view_interface { 
    using __interface = view_interface;
};
template<class T, class=void> INLINE_BOOL from_view_interface = false;
template<class T> INLINE_BOOL from_view_interface<T, void_t<typename T::__interface>> = derived_from<T, typename T::__interface>;
template<class T> INLINE_BOOL enable_view = derived_from<T, view_base> || from_view_interface<T>;
template<class T> concept view = range<T> && movable<T> && enable_view<T>;


// [iota.view]
template <class W, class B = unreachable_sentinel_t> class iota_view {
    struct S;
    struct I {
        using iterator_category = random_access_iterator_tag; // [[todo : input_iterator_tag]]
        using value_type = W;
        using difference_type = make_signed_t<decltype(W() - W())>;
        using pointer = void;
        using reference = W;

        I() = default;
        constexpr explicit I(W v) : v(v) {}

        constexpr W operator*() const { return v; }
        constexpr I& operator++() { ++v; return *this; }
        constexpr I operator++(int) { auto t = *this; ++*this; return t; }
        constexpr I& operator--() { --v; return *this; }
        constexpr I operator--(int) { auto t = *this; --*this; return t; }
        constexpr I& operator+=(difference_type n) {
            if constexpr (is_unsigned_v<W>)
                n >= difference_type(0) ? v += static_cast<W>(n) : v -= static_cast<W>(-n);
            else
                v += n;
            return *this;
        }
        constexpr I& operator-=(difference_type n) {
            if constexpr (is_unsigned_v<W>)
                n >= difference_type(0) ? v -= static_cast<W>(n) : v += static_cast<W>(-n);
            else
                v -= n;
            return *this;
        }
        constexpr W operator[](difference_type n) { return W(v + n); }

        friend constexpr bool operator==(const I& x, const I& y) { return x.v == y.v; }
        friend constexpr bool operator!=(const I& x, const I& y) { return x.v != y.v; }
        friend constexpr bool operator< (const I& x, const I& y) { return x.v <  y.v; }
        friend constexpr bool operator> (const I& x, const I& y) { return   y < x ; }
        friend constexpr bool operator<=(const I& x, const I& y) { return !(y < x); }
        friend constexpr bool operator>=(const I& x, const I& y) { return !(x < y); }

        friend constexpr I operator+(I i, difference_type n) { return i += n; }
        friend constexpr I operator+(difference_type n, I i) { return i += n; }
        friend constexpr I operator-(I i, difference_type n) { return i -= n; }
        friend constexpr difference_type operator-(const I& x, const I& y) {
            using D = difference_type;
            if constexpr (is_integral_v<W>) {
                if constexpr (is_signed_v<W>)
                   	 return D(D(x.v) - D(y.v));
                else
                    return (y.v > x.v) ? D(-D(y.v - x.v)) : D(x.v - y.v);
            } else
                return x.v - y.v;
        }
    private: 
        W v;
        friend S;
    };
    struct S {
    private:
        constexpr bool _M_equal(const I& x) const { return x.v == b; }
        B b;
    public:
        S() = default;
        constexpr explicit S(B b) : b(b) {}
        friend constexpr bool operator==(const I& x, const S& y) { return y._M_equal(x); }
        friend constexpr typename I::difference_type operator-(const I& x, const S& y) { return x.v - y.b; }
        friend constexpr typename I::difference_type operator-(const S& x, const I& y) { return -(y - x); }
    };
    W v;
    B b;
public:
    iota_view() = default;
    constexpr explicit iota_view(W v) : v(v) {}
    constexpr iota_view(type_identity_t<W> v, type_identity_t<B> b) : v(v), b(b) {}
    constexpr I begin() const { return I{v}; }
    constexpr auto end() const {
        if constexpr (is_same_v<W, B>)
            return I { b };
        else if constexpr (is_same_v<B, unreachable_sentinel_t>)
            return unreachable_sentinel;
        else
            return S { b };    
    }
    constexpr auto size() const {
        if constexpr (is_integral_v<W> && is_integral_v<B>)
            return v < 0 ? b < 0 ? to_unsigned(-v) - to_unsigned(-b) 
            : to_unsigned(b) + to_unsigned(-v) : to_unsigned(b) - to_unsigned(v);
        else
            return to_unsigned(b - v);
    }
};
template <class W, class B> iota_view(W, B) ->iota_view<W, B>;

    
namespace views {
struct iota_fn {
    template <class T> constexpr auto operator()(T&& e) const { return iota_view { FWD(e) }; }
    template <class T, class U> constexpr auto operator()(T&& e, U&& f) const { return iota_view { FWD(e), FWD(f) }; }
};
inline constexpr iota_fn iota;
}

namespace views {
struct zip_fn {
template<class R, class S>
    decltype(auto) operator()(R&& r, S&& s) const {
        struct Range {
            R r;
            S s;
            struct sentinel;
            struct iterator {
                iterator_t<R> r;
                iterator_t<S> s;
                constexpr pair<range_reference_t<R>, range_reference_t<S>>
                operator*() const { return { *r, *s }; }
                constexpr iterator& operator++() { ++r; ++s; return *this; }
                constexpr iterator operator++(int) { auto r = *this; ++*this; return r; }
                constexpr bool operator!=(const iterator& o) const { return r != o.r && s != o.s; }
                constexpr bool operator!=(const sentinel& o) const { return r != o.r && s != o.s; }
            };
            struct sentinel {
                sentinel_t<R> r;
                sentinel_t<S> s;
                constexpr bool operator!=(const iterator& o) const { return r != o.r && s != o.s; }
            };
            iterator begin() { return { std::begin(r), std::begin(s) }; }
            sentinel end() { return { std::end(r), std::end(s) }; }
        };
        return Range { (R&&)r, (S&&)s };
    }
};
inline constexpr zip_fn zip {};
} // namespace views
namespace views {
struct enumerate_fn {
    template<class R, enable_if_t<ranges::range<R>, int> =0> 
    decltype(auto) constexpr operator()(R&& r) const { return zip(iota(0), (R&&)r); }
    template<class R, enable_if_t<ranges::range<R>, int> =0> 
    friend constexpr decltype(auto) operator|(R&& r, enumerate_fn f) { return f(FWD(r)); }
};
inline constexpr enumerate_fn enumerate {};
} // namespace views

template<class T>
struct subset_view {
    struct iterator {
        using iterator_category = forward_iterator_tag;
        using value_type = T;
        using reference = T;
        using pointer = void;
        using difference_type = make_signed_t<decltype(T() - T())>;
        constexpr iterator(T t) noexcept : t(t), cur(t&(t-1)) {}
        constexpr iterator& operator++() noexcept { cur = (cur - 1) & t; return *this; }
        constexpr iterator operator++(int) noexcept { auto cp = *this; ++*this; return cp; }
        constexpr T operator*() const noexcept { return cur; }
        constexpr friend bool operator==(const iterator& i, const iterator& j) noexcept { return i.cur == j.cur; }
        constexpr friend bool operator!=(const iterator& i, const iterator& j) noexcept { return i.cur != j.cur; }
        constexpr friend bool operator==(const iterator& i, default_sentinel_t) noexcept { return i.cur == i.t; }
        constexpr friend bool operator==(default_sentinel_t, const iterator& i) noexcept { return i.cur == i.t; }
        constexpr friend bool operator!=(const iterator& i, default_sentinel_t) noexcept { return i.cur != i.t; }
        constexpr friend bool operator!=(default_sentinel_t, const iterator& i) noexcept { return i.cur != i.t; }
    private:
        T t, cur;
    };
    constexpr subset_view(T t) noexcept: t(t) {}
    constexpr iterator begin() const noexcept { return { t };  }
    constexpr default_sentinel_t end() const noexcept { return {}; }
    auto constexpr size() const noexcept { return to_unsigned(T{1})  << __popcount(t);  }
private:
    T t;
};
namespace views { // subset_view
struct subset_fn {
    template<class T, enable_if_t<is_integral_v<T>,int> =0>
    auto constexpr operator()(T t) const noexcept { return subset_view { t }; }
    template<class T, enable_if_t<is_integral_v<T>,int> =0>
    friend auto constexpr operator|(T t, subset_fn f) noexcept { return f(t); }
};
inline constexpr subset_fn subset {};
} // namespace views
template<class T> struct decompose_view {
    struct iterator {
        using iterator_category = forward_iterator_tag;
        using value_type = T;
        using reference = T;
        using pointer = void;
        using difference_type = make_signed_t<decltype(T() - T())>;
        void satisfy() noexcept { while (x % i != 0) { if (i * i > x) { i = x; break; } ++i; } }
        constexpr iterator(T x) noexcept : i(2), x(x) { satisfy(); }
        constexpr iterator& operator++() noexcept { x /= i; satisfy(); return *this; }
        constexpr iterator operator++(int) noexcept { auto cp = *this; ++*this; return cp; }
        constexpr T operator*() const noexcept { return i; }
        constexpr friend bool operator==(const iterator& i, const iterator& j) noexcept { return i.x == j.x && i.i == j.i; }
        constexpr friend bool operator!=(const iterator& i, const iterator& j) noexcept { return !(i==j); }
        constexpr friend bool operator==(const iterator& i, default_sentinel_t) noexcept { return i.x == 1; }
        constexpr friend bool operator==(default_sentinel_t, const iterator& i) noexcept { return i.x == 1; }
        constexpr friend bool operator!=(const iterator& i, default_sentinel_t) noexcept { return i.x != 1; }
        constexpr friend bool operator!=(default_sentinel_t, const iterator& i) noexcept { return i.x != 1; }
    private:
        T x, i;
    };
    constexpr decompose_view(T t) noexcept: t(t) {}
    constexpr iterator begin() const noexcept { return { t };  }
    constexpr default_sentinel_t end() const noexcept { return {}; }
private:
    T t;
};

namespace views {
struct decompose_fn { //decompose_view
    template<class T, enable_if_t<is_integral_v<T>,int> =0>
    auto constexpr operator()(T t) const noexcept { return decompose_view { t }; }
    template<class T, enable_if_t<is_integral_v<T>,int> =0>
    friend auto constexpr operator|(T t, decompose_fn f) noexcept { return f(t); }
};
inline constexpr decompose_fn decompose;
} // namespace views

} // namespace ranges
inline namespace print {
template<class T> struct brackets { T left; T right; }; template<class T> brackets(T, T)->brackets<T>;
template<class T> struct delim { T del; }; template<class T> delim(T)->delim<T>;

template<class Obj, class Bra> struct object_brackets { using _fmt = void; Obj& obj; Bra bra; };
template<class Obj, class Del> struct object_delim { using _fmt = void; Obj& obj; Del del; };
template<class Bra, class Del> struct brackets_delim { Bra bra; Del del; };
template<class Obj, class Bra, class Del> struct object_brackets_delim { using _fmt = void; Obj& obj; Bra bra; Del del; };

constexpr inline auto default_brackets = brackets { '[', ']' };
constexpr inline auto default_delim = delim { ',' };
constexpr inline auto et = delim { '\n' };
constexpr inline auto ebra = brackets { "", "" };

template<class Obj, class BraT> object_brackets<Obj, brackets<BraT>>
operator/(Obj&& o, brackets<BraT> bra) { return { o, bra }; }
template<class Obj, class DelT> object_delim<Obj, delim<DelT>>
operator/(Obj&& o, delim<DelT> del) { return { o, del }; }
template<class BraT, class DelT> brackets_delim<brackets<BraT>, delim<DelT>>
operator/(brackets<BraT> bra, delim<DelT> del) { return { bra, del }; }

template<class Obj, class BraT> object_brackets<Obj, brackets<BraT>> 
operator/(brackets<BraT> bra, Obj&& o) { return { o, bra }; }
template<class Obj, class DelT> object_delim<Obj, delim<DelT>> 
operator/(delim<DelT> del, Obj&& o) { return { o, del }; }
template<class BraT, class DelT> brackets_delim<brackets<BraT>, delim<DelT>>
operator/(delim<DelT> del, brackets<BraT> bra) { return { bra, del }; }


template<class Obj, class BraT, class DelT>  object_brackets_delim<Obj, brackets<BraT>, delim<DelT>> 
operator/(Obj&& o, brackets_delim<brackets<BraT>, delim<DelT>> bra_del) { return { o, bra_del.bra, bra_del.del }; }
template<class Obj, class BraT, class DelT>  object_brackets_delim<Obj, brackets<BraT>, delim<DelT>> 
operator/(brackets_delim<brackets<BraT>, delim<DelT>> bra_del, Obj&& o) { return { o, bra_del.bra, bra_del.del }; }
template<class Obj, class BraT, class DelT> object_brackets_delim<Obj, brackets<BraT>, delim<DelT>> 
operator/(object_brackets<Obj, brackets<BraT>> obj_bra, delim<DelT> del) { return { obj_bra.obj, obj_bra.bra, del }; }
template<class Obj, class BraT, class DelT> object_brackets_delim<Obj, brackets<BraT>, delim<DelT>> 
operator/(delim<DelT> del, object_brackets<Obj, brackets<BraT>> obj_bra) { return { obj_bra.obj, obj_bra.bra, del }; }
template<class Obj, class BraT, class DelT> object_brackets_delim<Obj, brackets<BraT>, delim<DelT>> 
operator/(object_delim<Obj, delim<DelT>> obj_del, brackets<BraT> bra) { return { obj_del.obj, bra, obj_del.del }; }
template<class Obj, class BraT, class DelT> object_brackets_delim<Obj, brackets<BraT>, delim<DelT>> 
operator/(brackets<BraT> bra, object_delim<Obj, delim<DelT>> obj_del) { return { obj_del.obj, bra, obj_del.del }; }
    
template<class R, class T = void>
using printable_range = enable_if_t<ranges::range<R> && !is_tuple_like<R> &&
    !is_any_of<ranges::range_value_t<R>, char, wchar_t, char16_t, char32_t>, T>;

namespace print_detail {
template<class, class = void> INLINE_BOOL has_del_impl = false;
template<class T> INLINE_BOOL has_del_impl<T, void_t<decltype(declval<T&>().del)>> = true;
template<class T> concept has_del = has_del_impl<remove_reference_t<T>>;
template<class, class = void> INLINE_BOOL has_bra_impl = false;
template<class T> INLINE_BOOL has_bra_impl<T, void_t<decltype(declval<T&>().bra)>> = true;
template<class T> concept has_bra = has_bra_impl<remove_reference_t<T>>;
}
template<class STRM, class T> struct RAII_brackets {
    STRM& os; T data;
    RAII_brackets(STRM& os, T data) : os(os), data(data) { os << data.left; }
    ~RAII_brackets() { os << data.right; }
};
template<class T> decltype(auto) _fmt(T&& t) {
    if constexpr (is_convertible_v<T, string_view>) return quoted(string_view(t));
    else if constexpr(is_same_v<decay_t<T>, char>) return quoted(string_view{ &t, 1 }, '\'');
    else return static_cast<T&&>(t);
}
template<class STRM, class Delim>
constexpr STRM& put_delim(STRM& os, bool ok, Delim d) { if (!ok) os << d.del << " "; return os; }
// [print.declaration]
template<class Ch, class Tr, class R, printable_range<R, int> = 0>
basic_ostream<Ch, Tr>& operator<<(basic_ostream<Ch, Tr>& os, R&& r);
template<class Ch, class Tr, class Tuple, class = void_t<typename tuple_size<Tuple>::type>>
basic_ostream<Ch, Tr>& operator<<(basic_ostream<Ch, Tr>& os, Tuple const& t);
template<class Ch, class Tr, template<class...> class W, class R, class... Rest, printable_range<R, int> = 0, 
class = void_t<typename W<R, Rest...>::_fmt>> basic_ostream<Ch, Tr>& operator<<(basic_ostream<Ch, Tr>& os, W<R, Rest...> w);
template<class Ch, class Tr, template<class...> class W, class Tp, class... Rest,
    class = void_t<typename tuple_size<remove_reference_t<Tp>>::type, typename W<Tp, Rest...>::_fmt>>
basic_ostream<Ch, Tr>& operator<<(basic_ostream<Ch, Tr>& os, W<Tp, Rest...> w);
//[print.impl]
template<class STRM, class Tuple, class Bra, class Del, std::size_t... Is>
void print_tuple_impl(STRM&& os, Tuple const& t, index_sequence<Is...>, Bra bra, Del delim)
{ RAII_brackets _ { os, bra }; ((put_delim(os, Is == 0, delim) << _fmt(get<Is>(t))), ...);  }
template<class STRM, class R, class Bra, class Del> void print_range_impl(STRM&& os, R&& r, Bra bra, Del del) 
{ RAII_brackets _ { os, bra }; size_t i = 0; for (auto&& elem : r) put_delim(os, ++i == 1, del) << _fmt(elem); }
//[print.operator<<]
template<class Ch, class Tr, class Tuple, class>
basic_ostream<Ch, Tr>& operator<<(basic_ostream<Ch, Tr>& os, Tuple const& t) {
    using Ind = make_index_sequence<tuple_size_v<remove_reference_t<Tuple>>>;
    print_tuple_impl(os, t, Ind {}, default_brackets, default_delim); return os;
}
template<class Ch, class Tr, class R, printable_range<R, int>>
basic_ostream<Ch, Tr>& operator<<(basic_ostream<Ch, Tr>& os, R&& r) 
{ print_range_impl(os, static_cast<R&&>(r), default_brackets, default_delim); return os; }
template<class Ch, class Tr, template<class...> class W, class R, class... Rest, printable_range<R, int>, class>
basic_ostream<Ch, Tr>& operator<<(basic_ostream<Ch, Tr>& os, W<R, Rest...> w) {
    using WW = W<R, Rest...>;
    auto del = [&] { if constexpr (print_detail::has_del<WW>) return w.del; else return default_delim; };
    auto bra = [&] { if constexpr (print_detail::has_bra<WW>) return w.bra; else return default_brackets; };
    print_range_impl(os, w.obj, bra(), del()); return os;
}
template<class Ch, class Tr, template<class...> class W, class Tp, class... Rest, class>
basic_ostream<Ch, Tr>& operator<<(basic_ostream<Ch, Tr>& os, W<Tp, Rest...> w) {
    using WW = W<Tp, Rest...>;
    auto del = [&] { if constexpr (print_detail::has_del<WW>) return w.del; else return default_delim; };
    auto bra = [&] { if constexpr (print_detail::has_bra<WW>) return w.bra; else return default_brackets; };
    using Indices = make_index_sequence<tuple_size_v<remove_reference_t<Tp>>>;
    print_tuple_impl(os, w.obj, Indices {}, bra(), del()); return os;
}
}

inline namespace safe {

static constexpr int ulp = 2;
template<class... T> using limits = numeric_limits<common_type_t<T...>>;
template<class TT, class UU> inline constexpr bool eq(TT&& t, UU&& u) {
    using T = remove_reference_t<TT>; using U = remove_reference_t<UU>;
    if constexpr (is_integral_v<T> && is_integral_v<U>) {
        if constexpr (is_signed_v<T> == is_signed_v<U>) return t == u;
        else if constexpr (is_signed_v<T>) return t < 0 ? false : to_unsigned(t) == u;
        else return u < 0 ? false : t == to_unsigned(u);
    } else if constexpr (is_floating_point_v<U> || is_floating_point_v<T>) {
        auto const x = abs(t - u); return x <= limits<T,U>::epsilon() * ulp || x < limits<T,U>::min();
    } else return t == u;
}
template<class TT, class UU> inline constexpr bool lt(TT&& t, UU&& u) {
    using T = remove_reference_t<TT>; using U = remove_reference_t<UU>;
    static_assert(is_floating_point_v<T> || is_floating_point_v<U>);
    if constexpr (is_integral_v<T> && is_integral_v<U>) {
        if constexpr (std::is_signed_v<T> == std::is_signed_v<U>)   return t < u;
        else if constexpr (std::is_signed_v<T>)                     return t < 0 ? true : to_unsigned(t) < u;
        else return u < 0 ? false : t < to_unsigned(u);
    } else if constexpr (is_floating_point_v<T> || is_floating_point_v<U>) {
        return eq(t, u) ? false : t < u;
    } else 
        return t < u;
}
 
template<class T> class sf { 
    T v = {};
public:
    sf() = default; template<class U> constexpr sf(U&& x) : v(FWD(x)) {}
    constexpr operator T() const { return v; }
};
template<class T> sf(T)->sf<T>; inline constexpr sf<ull> operator""_sf(ull x) { return x; }
inline constexpr sf<long double> operator""_sf(long double x) { return x; }

template<class L, class R> constexpr bool operator==(sf<L>const& l, sf<R>const& r) { return eq(L(l), R(r)); }
template<class L, class R> constexpr bool operator==(L const& l, sf<R>const& r) { return eq(l, R(r)); }
template<class L, class R> constexpr bool operator==(sf<L>const& l, R const& r) { return eq(L(l), r); }
template<class L, class R> constexpr bool operator!=(sf<L>const& l, sf<R>const& r) { return !eq(L(l), R(r)); }
template<class L, class R> constexpr bool operator!=(L const& l, sf<R>const& r) { return !eq(l, R(r)); }
template<class L, class R> constexpr bool operator!=(sf<L>const& l, R const& r) { return !eq(L(l), r); }
template<class L, class R> constexpr bool operator<(sf<L>const& l, sf<R>const& r) { return lt(L(l), R(r)); }
template<class L, class R> constexpr bool operator<(L const& l, sf<R>const& r) { return lt(l, R(r)); }
template<class L, class R> constexpr bool operator<(sf<L>const& l, R const& r) { return lt(L(l), r); }
template<class L, class R> constexpr bool operator>(sf<L>const& l, sf<R>const& r) { return lt(R(r), L(l)); }
template<class L, class R> constexpr bool operator>(L const& l, sf<R>const& r) { return lt(R(r), l); }
template<class L, class R> constexpr bool operator>(sf<L>const& l, R const& r) { return lt(r, L(l)); }
template<class L, class R> constexpr bool operator<=(sf<L>const& l, sf<R>const& r) { return !lt(R(r), L(l)); }
template<class L, class R> constexpr bool operator<=(L const& l, sf<R>const& r) { return !lt(R(r), l); }
template<class L, class R> constexpr bool operator<=(sf<L>const& l, R const& r) { return !lt(r, L(l)); }
template<class L, class R> constexpr bool operator>=(sf<L>const& l, sf<R>const& r) { return !lt(L(l), R(r)); }
template<class L, class R> constexpr bool operator>=(L const& l, sf<R>const& r) { return !lt(l, R(r)); }
template<class L, class R> constexpr bool operator>=(sf<L>const& l, R const& r) { return !lt(L(l), r); }
template<class T>constexpr enable_if_t<is_integral_v<T>, sf<make_signed_t<T>>> operator-(sf<T> r) { return -to_signed(T(r)); }
}

inline namespace numbers {
inline constexpr ll MOD = 998244353;
template<class T>inline constexpr auto e_v = static_cast<T>(2.71828182845904523542816810799394033892895095050334930419921875);
template<class T>inline constexpr auto pi_v = static_cast<T>(3.14159265358979323851280895940618620443274267017841339111328125);
template<class T>inline constexpr auto inf_v = static_cast<T>(0x3f3f3f3f3f3f3f3fll);
inline constexpr double e = e_v<double>;
inline constexpr double pi = pi_v<double>;
inline constexpr int inf = inf_v<int>;
}

inline namespace md {
template <auto M = long(1e9 + 7)> struct B {
    using L = decltype(M);
    L v;
    constexpr B(L x = 0) : v(x % M) {}
    template <class... T> using Q = enable_if_t<(is_integral_v<T> && ...), B>;
    template <class I, class = Q<I>> constexpr operator I() const { return I(v); }
    constexpr B &operator+=(B r) { v = (v + r.v) % M;return *this; }
    constexpr B &operator-=(B r) { v = ((v - r.v) % M + M) % M; return *this; }
    constexpr B &operator*=(B r) { v = (v * r.v) % M; return *this; }
    constexpr B &operator/=(B r) { *this *= r.inv(); return *this; }
    friend constexpr B operator+(B l, B r) { return l += r; }
    friend constexpr B operator-(B l, B r) { return l -= r; }
    friend constexpr B operator*(B l, B r) { return l *= r; }
    friend constexpr B operator/(B l, B r) { return l /= r; }
    template <class I> Q<I> friend constexpr operator+(I l, B r) { return (B)l += r; }
    template <class I> Q<I> friend constexpr operator-(I l, B r) { return (B)l -= r; }
    template <class I> Q<I> friend constexpr operator*(I l, B r) { return (B)l *= r; }
    template <class I> Q<I> friend constexpr operator/(I l, B r) { return (B)l /= r; }
    template <class I> Q<I> friend constexpr operator+(B l, I r) { return l += r; }
    template <class I> Q<I> friend constexpr operator-(B l, I r) { return l -= r; }
    template <class I> Q<I> friend constexpr operator*(B l, I r) { return l *= r; }
    template <class I> Q<I> friend constexpr operator/(B l, I r) { return l /= r; }
    constexpr B operator+() const { return *this; }
    constexpr B operator-() const { return 0 - *this; }
    friend constexpr B inv(B x) { return x.inv(); }
    template <class I> Q<I> friend constexpr pow(B l, I r) { return l.pow(r); }
    constexpr B inv() const { return pow(M - 2); }
    template <class I> Q<I> constexpr pow(I r) const 
    { B b = *this, x = 1; while (r) { if (r & 1) x *= b; b *= b; r /= 2; } return x; }
    template <class L, class R> Q<L, R> static constexpr pow(L l, R r) { return B(l).pow(r); }
    template <class I> Q<I> static fac(I r) {
        static unordered_map<I, B> f{{0, 1}};
        if (auto i = f.find(r); i != end(f)) return i->second;
        return f[r] = r * fac(r - 1);
    }
    template <class I> Q<I> static comb(I x, I y) { return fac(x) / fac(y) / fac(x - y); }
    constexpr B &operator++() { return *this += 1; }
    constexpr B &operator--() { return *this -= 1; }
};
template <auto M> using basic_mod = B<M>;  using mod = B<>;
inline constexpr mod operator""_m(unsigned long long x) { return mod(x); }
}

inline namespace unionfind {
class UF {
    std::vector<int> fa, sz;
    std::size_t n, comp_cnt;
public:
    UF(std::size_t n): n(n), comp_cnt(n), fa(n), sz(n, 1) {
        std::iota(begin(fa), end(fa), 0);
    }
    auto size() { return n; }
    auto count() { return comp_cnt; }
    int findset(int x) { return fa[x] == x ? x : fa[x] = findset(fa[x]); }
    void unite(int x, int y) {
        if (sz[x] < sz[y]) swap(x, y);
        fa[y] = x;
        sz[x] += sz[y];
        --comp_cnt;
    }
    bool findAndUnite(int x, int y) {
        int x0 = findset(x), y0 = findset(y);
        if (x0 != y0) unite(x0, y0);
        return x0 != y0;
    }
};
}

inline namespace utility {
namespace udetail {
    template<class,class=void> INLINE_BOOL has_top = false;
    template<class T> INLINE_BOOL has_top<T, void_t<decltype(declval<T>().top())>> = true;
}

constexpr auto pop = [](auto& t) {
    using T = decay_t<decltype(t)>;
    auto __g = [&]()->auto&& { if constexpr (udetail::has_top<T>) return t.top(); else return t.front(); };
    auto ret = move(const_cast<typename T::value_type&>(__g()));
    t.pop(); return ret;
};

inline namespace functional {
template<class Fun> class Y_combinator {     
	Fun fun_; 
public:
	template<class F> Y_combinator(F&& fun): fun_(FWD(fun)) {}     
	template<class... Args> decltype(auto) operator()(Args&&...args) const { return fun_(*this, (Args&&)args...); }
};
template< class T > Y_combinator(T) -> Y_combinator<T>;
constexpr inline auto bit_view = [](auto&& t) {
    return string_view { reinterpret_cast<char const*>(addressof(t)), sizeof(t) };
};
struct bit_hash {
    template<class T>
    size_t operator() (T&& t) const { return hash<string_view> {} (bit_view(t)); }
};
struct bit_equal {
    template<class T, class U>
    bool operator() (T&& t, U&& u) const { return bit_view(t) == bit_view(u); }
};
} // namespace functional
} // namespace utility

inline namespace direction {
constexpr int dir [][2] { {0,1}, {1,0}, {0,-1}, {-1,0} };
constexpr int dir8[][2] { {0,1}, {1,0}, {0,-1}, {-1,0}, {1,1}, {-1,1}, {1,-1}, {-1,-1} };
constexpr auto valid = [](auto m, auto n) { return [=](size_t x, size_t y) { return x < m && y < n; }; };
}
inline namespace init {
#ifdef __cpp_lib_memory_resource
inline constexpr auto set_pmr = [] {
    static byte buffer [1 << 30];
    static auto pool = pmr::monotonic_buffer_resource { data(buffer), size(buffer) };
    set_default_resource(&pool);
    return 0;
};
#endif
inline constexpr auto set_fast_io = [] { 
    ios::sync_with_stdio(false); cin.tie(nullptr); cout.tie(nullptr); cout << setprecision(12); return 0;
};

} // namespace init
} // namespace my
namespace std {
template<class> concept is_vector_v = false; template<class T> concept is_vector_v<vector<T>> = true;
template<class T> struct tuple_size<vector<T>> : integral_constant<size_t, vector_size_v> {};
template<size_t I, class T>struct tuple_element<I, vector<T>> : enable_if<true, T> {};
template<size_t I, class T, enable_if_t<is_vector_v<decay_t<T>>, int> = 0>
decltype(auto) get(T&& t) { return static_cast<T&&>(t)[I]; }
} // namespace std
inline namespace simplify {
    namespace rg = ranges;
    namespace vw = ranges::views;
    inline constexpr ranges::views::iota_fn range {};
    inline constexpr ranges::views::zip_fn zp {};
    inline constexpr ranges::views::enumerate_fn en {};
    inline constexpr ranges::views::subset_fn subset{};
    #define Yc Y_combinator
} // namespace simplify
