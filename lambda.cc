#define FWD(...) std::forward<decltype(__VA_ARGS__)>(__VA_ARGS__)
struct deleted_t {};
template <size_t>
deleted_t pack_get() {
    return {};
}
template <size_t X, class H, class... A>
decltype(auto) pack_get(H&& h, A&&... a) {
    if constexpr (X == 0)
        return FWD(h);
    else
        return pack_get<X - 1>(FWD(a)...);
}
#define La(...)                             \
    [&](auto&&... a) -> decltype(auto) {    \
        auto&& _1 = pack_get<0>(FWD(a)...); \
        auto&& _2 = pack_get<1>(FWD(a)...); \
        auto&& _3 = pack_get<2>(FWD(a)...); \
        auto&& _4 = pack_get<3>(FWD(a)...); \
        return __VA_ARGS__;                 \
    }
