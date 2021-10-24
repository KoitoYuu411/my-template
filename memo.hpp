template<class,template <class...>class=map>struct Hmemo{};
template <template<class...>class M, class R, class...A>struct Hmemo<R(A...),M>{
template<class F>struct fn{
fn(F f):f(move(f)){}using T=tuple<decay_t<A>...>;mutable M<T,R> m;F f;
template<class...S>R const& operator()(S&&...s)const{
auto t=T(s...);auto i=m.find(t);if(i==m.end())i=m.emplace((T&&)t,invoke(f,ref(*this),(S&&)s...)).first;return (i->second);
}
};
template<class F>fn(F)->fn<F>;
};
#define memo(...) Hmemo<__VA_ARGS__>::fn
