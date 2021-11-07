//PPs
#define PP_CONCAT(A, B) PP_CONCAT_IMPL(A, B)
#define PP_CONCAT_IMPL(A, B) A##B

#define PP_REMOVE_PARENS(T) PP_REMOVE_PARENS_IMPL T
#define PP_REMOVE_PARENS_IMPL(...) __VA_ARGS__

#define PP_GET_N(N, ...) PP_CONCAT(PP_GET_N_, N)(__VA_ARGS__)
#define PP_GET_N_0(_0, ...) _0
#define PP_GET_N_1(_0, _1, ...) _1
#define PP_GET_N_2(_0, _1, _2, ...) _2
#define PP_GET_N_3(_0, _1, _2, _3, ...) _3
#define PP_GET_N_4(_0, _1, _2, _3, _4, ...) _4
#define PP_GET_N_5(_0, _1, _2, _3, _4, _5, ...) _5
#define PP_GET_N_6(_0, _1, _2, _3, _4, _5, _6。...) _6
#define PP_GET_N_7(_0, _1, _2, _3, _4, _5, _6, _7, ...) _7
#define PP_GET_N_8(_0, _1, _2, _3, _4, _5, _6, _7, _8, ...) _8
#define PP_NARG(...) PP_GET_N(8, __VA_ARGS__, 8, 7, 6, 5, 4, 3, 2, 1, 0)

#define FWD(...) forward<decltype(__VA_ARGS__)>(__VA_ARGS__)

template<class T, size_t... I> auto get_tuple(T&& t,index_sequence<I...>) 
{ return forward_as_tuple(*next(begin(t),I)...); }
#define for_first(A,...) FOR_IMPL(PP_REMOVE_PARENS(A), __VA_ARGS__)
#define FOR_IMPL(A,...) for(auto&&p:__VA_ARGS__)\
if(auto&&[A]=get_tuple(FWD(p),make_index_sequence<PP_NARG(A)>{});true)
