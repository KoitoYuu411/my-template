#include <bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
inline constexpr size_t vector_size_v = 2;
inline namespace my {
#define debug(...) cout << #__VA_ARGS__ << "\t" << forward_as_tuple(__VA_ARGS__)/ebra << endl;
#define ALL(...) begin(__VA_ARGS__), end(__VA_ARGS__)
#define RALL(...) rbegin(__VA_ARGS__), rend(__VA_ARGS__)
#define FWD(...) static_cast<decltype(__VA_ARGS__)&&>(__VA_ARGS__)
#define DCLV(...) declval<__VA_ARGS__>()
#define DCLT(...) decltype(__VA_ARGS__)
#define RET(...) { return __VA_ARGS__ ; }
#define NOEXP(...) noexcept(noexcept(__VA_ARGS__))
#define NOEXP_RET(...) NOEXP(__VA_ARGS__) RET(__VA_ARGS__)
#define DCLT_RET(...) -> DCLT(__VA_ARGS__) RET(__VA_ARGS__)
#define NOEXP_DCLT_RET(...) NOEXP(__VA_ARGS__) DCLT(__VA_ARGS__)

#define NP namespace 
#define CL class
#define ST struct
#define TP template
#define TPP TP<CL...>CL
#define CEXP constexpr
#define IC inline CEXP
#define FC friend CEXP
#define COP CEXP operator
#define FCOP friend CEXP operator

#define CPO CEXP inline auto
#define concept IC bool

#define Req(...) std::enable_if_t<__VA_ARGS__, int>
#define Reqs(...) Req(__VA_ARGS__) {}
#define TpReqt(...) Req(__VA_ARGS__) = 0>
#define TpReq(...) TP< __VA_ARGS__ , TpReqt

#define LazyReq(Name) TP<CL Name##Name = Name , TpReqt

#define Def_Suffix(OP) { auto t=*this; OP *this; return t; }

using NP std;
using ull = unsigned long long;
NP pbds_detail { using NP __gnu_pbds;
TP<CL T,CL V=null_type,CL C=less<>>using order_tree = tree<T, V, C, rb_tree_tag, tree_order_statistics_node_update>;
} // pbds_detail
using pbds_detail::order_tree;
inline NP type_traits {
ST __empty {};
TP<CL,CL...>auto _req_impl(...)->false_type;
TP<CL R, CL... A,CL=decltype(&R::TP freq<A...>)>auto _req_impl(int)->true_type;
TP<CL R, CL... A> IC bool requires_ = decltype(_req_impl<R, A...>(0))::value;
TP<bool Expr,CL T=int> using requires_expr = enable_if_t<Expr, T>;
TP<size_t I> ST tag : tag<I - 1>{}; TP<>ST tag<0> {};
//[remove.cvref]
TP<CL T>ST type_identity { using type = T;};
TP<CL T>using type_identity_t = typename type_identity<T>::type;
TP<CL T>ST remove_cvref : remove_cv<remove_reference_t<T>> {};
TP<CL T>using remove_cvref_t = typename remove_cvref<T>::type;
//[common.reference]
TP<TPP AliasT, CL... A>auto exists_helper(long) -> false_type;
TP<TPP AliasT, CL... A, CL = AliasT<A...>> auto exists_helper(int) -> true_type;
TP<TPP AliasT, CL... A>
IC bool exists_v = decltype(exists_helper<AliasT, A...>(0))::value;
NP common_detail { 
TP<CL...>ST common_type;
TP<CL T, CL U>ST copy_cv:type_identity<U>{};
TP<CL T, CL U>ST copy_cv<const T, U>:type_identity<add_const_t<U>>{};
TP<CL T, CL U>ST copy_cv<volatile T, U>:type_identity<add_volatile_t<U>>{};
TP<CL T, CL U>ST copy_cv<const volatile T, U>:type_identity_t<add_cv_t<U>>{};
TP<CL T, CL U>using copy_cv_t = typename copy_cv<T, U>::type;
TP<CL T>using cref_t = add_lvalue_reference_t<const remove_reference_t<T>>;
TP<CL T, CL U>using cond_res_t = decltype(true? DCLV(T(&)())() : DCLV(U(&)())());
// For some value of "simple"
TP<CL A, CL B, CL = remove_reference_t<A>,CL=remove_reference_t<B>, CL = void> ST common_ref {};
TP<CL A, CL B>using common_ref_t = typename common_ref<A, B>::type;
TP<CL A, CL B, CL=remove_reference_t<A>,CL=remove_reference_t<B>, CL=void> ST lval_common_ref {};
TP<CL A, CL B, CL X, CL Y>
ST lval_common_ref<A, B, X, Y, enable_if_t<is_reference_v<cond_res_t<copy_cv_t<X, Y>&, copy_cv_t<Y, X>&>>>> 
{ using type = cond_res_t<copy_cv_t<X, Y>&, copy_cv_t<Y, X>&>; };
TP<CL A, CL B> using lval_common_ref_t = typename lval_common_ref<A, B>::type;
TP<CL A, CL B, CL X, CL Y> ST common_ref<A&, B&, X, Y> : lval_common_ref<A&, B&> {};
TP<CL X, CL Y> using rref_cr_helper_t = remove_reference_t<lval_common_ref_t<X&, Y&>>&&;
TP<CL A, CL B, CL X, CL Y> ST common_ref<A&&, B&&, X, Y, enable_if_t<
is_convertible_v<A&&, rref_cr_helper_t<X, Y>> &&is_convertible_v<B&&, rref_cr_helper_t<X, Y>>>>
{ using type = rref_cr_helper_t<X, Y>; };
TP<CL A, CL B, CL X, CL Y> ST common_ref<A&&, B&, X, Y, enable_if_t<
    is_convertible_v<A&&, lval_common_ref_t<const X&, Y&>>>>
{ using type = lval_common_ref_t<const X&, Y&>; };
TP<CL A, CL B, CL X, CL Y> ST common_ref<A&, B&&, X, Y> : common_ref<B&&, A&> {};
TP<CL> ST xref { TP<CL U> using type = U; };
TP<CL A> ST xref<A&> { TP<CL U> using type = add_lvalue_reference_t<typename xref<A>::TP type<U>>; };
TP<CL A> ST xref<A&&> { TP<CL U> using type = add_rvalue_reference_t<typename xref<A>::TP type<U>>; };
TP<CL A> ST xref<const A> { TP<CL U> using type = add_const_t<typename xref<A>::TP type<U>>; };
TP<CL A> ST xref<volatile A> { TP<CL U> using type = add_volatile_t<typename xref<A>::TP type<U>>; };
TP<CL A> ST xref<const volatile A> { TP<CL U> using type = add_cv_t<typename xref<A>::TP type<U>>; };
TP<CL T, CL U, TP<CL> CL TQual,TP<CL> CL UQual> ST basic_common_reference {};
TP<CL...> ST common_reference;
TP<CL... Ts> using common_reference_t = typename common_reference<Ts...>::type;
TP<> ST common_reference<> {};
TP<CL T0> ST common_reference<T0> { using type = T0; };
TP<CL T, CL U> IC bool has_common_ref_v = exists_v<common_ref_t, T, U>;
TP<CL T, CL U> using basic_common_ref_t = typename basic_common_reference<remove_cvref_t<T>, remove_cvref_t<U>,
xref<T>::TP type, xref<U>::TP type>::type;
TP<CL T, CL U> IC bool has_basic_common_ref_v = exists_v<basic_common_ref_t, T, U>;
TP<CL T, CL U> IC bool has_cond_res_v = exists_v<cond_res_t, T, U>;
TP<CL T, CL U, CL = void> ST binary_common_ref : common_type<T, U> {};
TP<CL T, CL U> ST binary_common_ref<T, U, enable_if_t<has_common_ref_v<T, U>>>: common_ref<T, U> {};
TP<CL T, CL U> ST binary_common_ref<T, U, enable_if_t<has_basic_common_ref_v<T, U> && !has_common_ref_v<T, U>>>
{ using type = basic_common_ref_t<T, U>; };
TP<CL T, CL U>
ST binary_common_ref<T, U, enable_if_t<has_cond_res_v<T, U> && !has_basic_common_ref_v<T, U> && !has_common_ref_v<T, U>>>
{ using type = cond_res_t<T, U>; };
TP<CL T1, CL T2>ST common_reference<T1, T2> : binary_common_ref<T1, T2> { };
TP<CL Void, CL T1, CL T2, CL... Rest> ST multiple_common_reference {};
TP<CL T1, typename T2, CL... Rest> ST multiple_common_reference
    <void_t<common_reference_t<T1, T2>>, T1, T2, Rest...>: common_reference<common_reference_t<T1, T2>, Rest...> {};
TP<CL T1,CL T2,CL... R> ST common_reference<T1, T2, R...>: multiple_common_reference<void, T1, T2, R...> {};
// [common.type]
TP<CL...> ST common_type;
TP<CL... Ts> using common_type_t = typename common_type<Ts...>::type;
TP<CL T, CL U>
CEXP bool same_decayed_v = is_same<T, decay_t<T>>::value && is_same<U, decay_t<U>>::value;
TP<CL T, CL U> using ternary_return_t = decay_t<decltype(false ? DCLV(T) : DCLV(U))>;
TP<CL, CL, CL=void> ST binary_common_type {};
TP<CL T, CL U>
ST binary_common_type<T, U, enable_if_t<!same_decayed_v<T, U>>> : common_type<decay_t<T>, decay_t<U>> {};
TP<CL T, CL U>
ST binary_common_type<T, U, enable_if_t<same_decayed_v<T, U> && exists_v<ternary_return_t, T, U>>> 
{ using type = ternary_return_t<T, U>; };
TP<CL T, CL U>
ST binary_common_type<T, U, enable_if_t<
same_decayed_v<T, U> && !exists_v<ternary_return_t, T, U> && exists_v<cond_res_t, cref_t<T>, cref_t<U>>>> 
{ using type = decay_t<cond_res_t<cref_t<T>, cref_t<U>>>; };
TP<> ST common_type<> {};
TP<CL T> ST common_type<T> : common_type<T, T> {};
TP<CL T, CL U> ST common_type<T, U>: binary_common_type<T, U> {};
TP<CL Void, CL...> ST multiple_common_type {};
TP<CL T1, CL T2, CL... R> ST multiple_common_type<void_t<common_type_t<T1, T2>>, T1, T2, R...> 
    : common_type<common_type_t<T1, T2>, R...> {};
TP<CL T1, CL T2, CL... R> ST common_type<T1, T2, R...> : multiple_common_type<void, T1, T2, R...> {};
} // common_detail
using common_detail::common_reference;
using common_detail::common_reference_t;
TP<CL T, CL... A> concept is_any_of = ( is_same_v<T, A> || ... );
TP<CL T, CL = void> IC bool is_tuple_like = false;
TP<CL T> IC bool is_tuple_like<T, void_t<decltype(tuple_size<T> {})>> = true;
TP<CL T> concept tuple_like = is_tuple_like<remove_reference_t<T>>;    
}
inline NP concepts {
//[concept.same]
TP<CL T, CL U> concept same_as=is_same_v<T, U>;
//[concept.derived]
ST derived_from_ { TP<CL D, CL B> auto freq()->requires_expr<is_convertible_v<const volatile D*, const volatile B*>>; };
TP<CL D, CL B> concept derived_from = is_base_of_v<B, D> && requires_<derived_from_,D,B>;
// [concept.convertible]
ST convertible_to_concept 
{ TP<CL From, CL To> auto freq(add_rvalue_reference_t<From> (&f)())->decltype(static_cast<To>(f())); };
TP<CL From, CL To>concept convertible_to =is_convertible_v<From, To>&&requires_<convertible_to_concept, From, To>;
// [concept.commonref]
ST common_reference_with_ { 
    TP<CL T, CL U>static auto freq() -> requires_expr<same_as<common_reference_t<T, U>, common_reference_t<U, T>>
    && convertible_to<T, common_reference_t<T, U>> && convertible_to<U, common_reference_t<T, U>>>; 
};
TP<CL T, CL U>concept common_reference_with= requires_<common_reference_with_,T, U>;
// [concepts.common]
ST common_with_ {
TP<CL T, CL U>auto freq()->
    decltype(static_cast<common_type_t<T, U>>(DCLV(T)),static_cast<common_type_t<T, U>>(DCLV(U)));
TP<CL, CL>static auto test(long) -> false_type;
TP<CL T, CL U> static auto test(int) -> enable_if_t<
    same_as<common_type_t<T, U>, common_type_t<U, T>> && requires_<common_with_, T, U> &&
    common_reference_with<add_lvalue_reference_t<const T>,add_lvalue_reference_t<const U>> &&
    common_reference_with<add_lvalue_reference_t<common_type_t<T, U>>,
    common_reference_t<add_lvalue_reference_t<const T>,add_lvalue_reference_t<const U>>>, true_type>;
};
TP<CL T, CL U>concept common_with =decltype(common_with_::test<T, U>(0))::value;
// [concept.arithmetic]
TP<CL T>concept integral = is_integral_v<T>;
TP<CL T>concept signed_integral = integral<T> && is_signed_v<T>;
TP<CL T>concept unsigned_integral = integral<T> && !signed_integral<T>;
TP<CL T>concept floating_point = is_floating_point_v<T>;
// [concept.assignable]
ST assignable_from_ {
TP<CL L,CL R>auto freq(L l, R&&r)->decltype(requires_expr<same_as<decltype(l=FWD(r)), L>>{});
    TP<CL, CL>static auto test(long) -> false_type;
    TP<CL L, CL R>static auto test(int) -> enable_if_t<
        is_lvalue_reference_v<L> &&common_reference_with<const remove_reference_t<L>&,const remove_reference_t<R>&> &&
        requires_<assignable_from_, L, R>, true_type>;
};
TP<CL L, CL R>
concept assignable_from=decltype(assignable_from_::test<L, R>(0))::value;
// [concept.destructible]
TP<CL T>concept destructible = is_nothrow_destructible_v<T>;
// [concept.constructible]
TP<CL T, CL... A>concept constructible_from=destructible<T> && is_constructible_v<T, A...>;
// [concept.default.init]
TP<CL, CL=void>IC bool is_default_initializable = false;
// Thanks to Damian Jarek on Slack for this formulation
TP<CL T>IC bool is_default_initializable<T, void_t<decltype(::new T)>> = true;
ST default_initializable_concept {TP<CL T, CL = decltype(T{})>auto freq() -> void;};
TP<CL T> concept default_initializable =
    constructible_from<T> && requires_<default_initializable_concept, T> && is_default_initializable<T>;
// [concept.moveconstructible]
TP<CL T>concept move_constructible = constructible_from<T, T> && convertible_to<T, T>;
// [concept.copyconstructible]
ST copy_constructible_concept {
TP<CL>static auto test(long) -> false_type;
TP<CL T>static auto test(int) -> enable_if_t<
    move_constructible<T> &&constructible_from<T, T&> && convertible_to<T&, T> && constructible_from<T, const T&>
    && convertible_to<const T&, T> && constructible_from<T, const T> && convertible_to<const T, T>, true_type>;
};
TP<CL T> concept copy_constructible = decltype(copy_constructible_concept::test<T>(0))::value;
// [range.swap]
NP swap_ {
TP<CL T>void swap(T&, T&) = delete;
TP<CL T, size_t N>void swap(T (&)[N], T (&)[N]) = delete;
ST fn { private:
TP<CL T, CL U> static CEXP auto impl(T&& t, U&& u, tag<2>) noexcept(
noexcept(swap(FWD(t), FWD(u))))-> decltype(static_cast<void>(swap(FWD(t),FWD(u))))
{ (void) swap(FWD(t), FWD(u)); }
TP<CL T, CL U, size_t N, CL F = fn> static CEXP auto impl(T (&t)[N], U (&u)[N], tag<1>)
noexcept(noexcept(DCLV(F&)(*t, *u)))-> decltype(DCLV(F&)(*t, *u))
{ for (size_t i = 0; i < N; ++i) fn::impl(t[i], u[i], tag<2>{}); }
TP<CL T> static CEXP auto impl(T& a, T& b, tag<0>) 
noexcept(is_nothrow_move_constructible<T>::value&& is_nothrow_assignable<T&, T>::value)-> enable_if_t<
move_constructible<T> && assignable_from<T&, T>> { T temp = move(a); a = move(b); b = move(temp); }
public: TP<CL T, CL U> auto COP ()(T&& t, U&& u) const
noexcept(noexcept(fn::impl(FWD(t), FWD(u), tag<2>{}))) -> decltype(fn::impl(FWD(t), FWD(u), tag<2>{}))
{ return fn::impl(FWD(t), FWD(u), tag<2>{}); }
};
} // end NP swap_
IC swap_::fn my_swap;
// [concept.swappable]
ST swappable_concept { TP<CL T>auto freq(T& a, T& b) -> decltype(my_swap(a, b)); };
TP<CL T>concept swappable = requires_<swappable_concept, T>;
ST swappable_with_concept {
TP<CL T, CL U>auto freq(T&& t, U&& u) -> decltype(
    my_swap(FWD(t), FWD(t)), my_swap(FWD(u), FWD(u)), my_swap(FWD(t), FWD(u)), my_swap(FWD(u), FWD(t)) );
TP<CL, CL>static auto test(long) -> false_type;
TP<CL T, CL U>static auto test(int) -> enable_if_t<
    common_reference_with<const remove_reference_t<T>&,const remove_reference_t<U>&> &&
    requires_<swappable_with_concept, T, U>,true_type>;
};
TP<CL T, CL U> concept swappable_with =decltype(swappable_with_concept::test<T, U>(0))::value;
// [concept.boolean_testable]
TP<CL T>concept boolean_testable_impl = convertible_to<T, bool>;
ST boolean_testable_concept
{ TP<CL T>auto freq(T&& t) ->requires_expr<boolean_testable_impl<decltype(!FWD(t))>>; };
TP<CL T> concept boolean_testable =boolean_testable_impl<T>&&requires_<boolean_testable_concept, T>;
// [concept.equalitycomparable]
ST weakly_equality_comparable_with_concept {
TP<CL T, CL U> auto freq(const remove_reference_t<T>& t, const remove_reference_t<U>& u)->decltype(
requires_expr<boolean_testable<decltype(t == u)>>{},requires_expr<boolean_testable<decltype(t != u)>>{},
requires_expr<boolean_testable<decltype(u == t)>>{},requires_expr<boolean_testable<decltype(u != t)>>{});
};
TP<CL T, CL U>concept weakly_equality_comparable_with = requires_<weakly_equality_comparable_with_concept, T, U>;
TP<CL T>concept equality_comparable = weakly_equality_comparable_with<T, T>;
ST equality_comparable_with_concept {
TP<CL, CL> static auto test(long) -> false_type;
TP<CL T, CL U>static auto test(int) -> enable_if_t< equality_comparable<T> && equality_comparable<U> && 
common_reference_with<const remove_reference_t<T>&, const remove_reference_t<U>&> &&
    equality_comparable<common_reference_t<const remove_reference_t<T>&,const remove_reference_t<U>&>> &&
    weakly_equality_comparable_with<T, U>, true_type>;
};
TP<CL T, CL U>concept equality_comparable_with =decltype(equality_comparable_with_concept::test<T, U>(0))::value;
// [concepts.totallyordered]
ST partially_ordered_with_concept {
    TP<CL T, CL U> auto freq(const remove_reference_t<T>& t, const remove_reference_t<U>& u)->decltype(
        requires_expr<boolean_testable<decltype(t < u)>>{},requires_expr<boolean_testable<decltype(t > u)>>{},
        requires_expr<boolean_testable<decltype(t <= u)>>{},requires_expr<boolean_testable<decltype(t >= u)>>{},
        requires_expr<boolean_testable<decltype(u < t)>>{},requires_expr<boolean_testable<decltype(u > t)>>{},
        requires_expr<boolean_testable<decltype(u <= t)>>{},requires_expr<boolean_testable<decltype(u >= t)>>{});
};
TP<CL T, CL U>concept partially_ordered_with =requires_<partially_ordered_with_concept, T, U>;
TP<CL T> concept totally_ordered =equality_comparable<T> && partially_ordered_with<T, T>;
ST totally_ordered_with_concept {
    TP<CL, CL>static auto test(long)->false_type;
    TP<CL T, CL U> static auto test(int)->enable_if_t< 
    totally_ordered<T> && totally_ordered<U> && equality_comparable_with<T, U> && 
    totally_ordered<common_reference_t<const remove_reference_t<T>&,const remove_reference_t<U>&>> &&
    partially_ordered_with<T, U>, true_type>;
};
TP<CL T, CL U>concept totally_ordered_with =decltype(totally_ordered_with_concept::test<T, U>(0))::value;

inline NP invoke_ {
TP<CL>CEXP bool is_reference_wrapper_v = false;
TP<CL T> CEXP bool is_reference_wrapper_v<reference_wrapper<T>> = true;
ST fn { private:
    TP<CL Base, CL T, CL Derived, CL... A> static CEXP auto
    impl(T Base::*pmf, Derived&& ref, A&&... a) 
        noexcept(noexcept((FWD(ref).*pmf)(FWD(a)...)))
        -> enable_if_t<is_function<T>::value && is_base_of<Base, decay_t<Derived>>::value,
        decltype((FWD(ref).*pmf)(FWD(a)...))>
    { return (FWD(ref).*pmf)(FWD(a)...); } 
    TP<CL Base, CL T, CL RefWrap, CL... A> static CEXP auto
    impl(T Base::*pmf, RefWrap&& ref, A&&... a) 
    noexcept(noexcept((ref.get().*pmf)(FWD(a)...)))
        -> enable_if_t<is_function<T>::value && is_reference_wrapper_v<decay_t<RefWrap>>,
  decltype((ref.get().*pmf)(FWD(a)...))>
    { return (ref.get().*pmf)(FWD(a)...); }
    TP<CL Base, CL T, CL Pointer, CL... A> static CEXP auto
    impl(T Base::*pmf, Pointer&& ptr, A&&... a) 
    noexcept(noexcept(((*FWD(ptr)).*pmf)(FWD(a)...)))
        -> enable_if_t<is_function<T>::value &&!is_reference_wrapper_v<decay_t<Pointer>> &&
  !is_base_of<Base, decay_t<Pointer>>::value,
        decltype(((*FWD(ptr)).*pmf)(FWD(a)...))>
    { return ((*FWD(ptr)).*pmf)(FWD(a)...); }
    TP<CL Base, CL T, CL Derived> static CEXP auto
    impl(T Base::*pmd, Derived&& ref) noexcept(noexcept(FWD(ref).*pmd))
        -> enable_if_t<!is_function<T>::value && is_base_of<Base, decay_t<Derived>>::value,
        decltype(FWD(ref).*pmd)> { return FWD(ref).*pmd; }
    TP<CL Base, CL T, CL RefWrap>
    static CEXP auto impl(T Base::*pmd, RefWrap&& ref) noexcept(noexcept(ref.get().*pmd))
        -> enable_if_t<!is_function<T>::value && is_reference_wrapper_v<decay_t<RefWrap>>,
        decltype(ref.get().*pmd)> { return ref.get().*pmd; }
    TP<CL Base, CL T, CL Pointer> static CEXP auto
    impl(T Base::*pmd, Pointer&& ptr) noexcept(noexcept((*FWD(ptr)).*pmd))
        -> enable_if_t< !is_function<T>::value && !is_reference_wrapper_v<decay_t<Pointer>> &&
    !is_base_of<Base, decay_t<Pointer>>::value,
    decltype((*FWD(ptr)).*pmd)> { return (*FWD(ptr)).*pmd; }
    TP<CL F, CL... A>
    static CEXP auto impl(F&& f, A&&... a) noexcept(
        noexcept(FWD(f)(FWD(a)...)))
        -> enable_if_t< !is_member_pointer<decay_t<F>>::value, decltype(forward<F>(f)(FWD(a)...))>
    { return FWD(f)(FWD(a)...); }
public:
    TP<CL F, CL... A> auto COP ()(F&& f, A&&... a) const noexcept(
        noexcept(fn::impl(FWD(f), FWD(a)...)))
        -> decltype(fn::impl(FWD(f), FWD(a)...))
    { return fn::impl(FWD(f), FWD(a)...); }
};
} // invoke_

IC invoke_::fn my_invoke;
TP<CL Void, CL, CL...> ST invoke_result_helper {};
TP<CL F, CL... A>
ST invoke_result_helper<void_t<decltype(my_invoke(DCLV(F), DCLV(A)...))>,F, A...> {
    using type = decltype(my_invoke(DCLV(F), DCLV(A)...));
};
TP<CL F, CL... A> ST invoke_result : invoke_result_helper<void, F, A...> {};
TP<CL F, CL... A>using invoke_result_t = typename invoke_result<F, A...>::type;
// [concept.movable]
TP<CL T> concept movable = is_object_v<T> && move_constructible<T> && assignable_from<T&, T> && swappable<T>;
// [concept.copyable]
TP<CL T>concept copyable = copy_constructible<T> && movable<T> &&
    assignable_from<T&, T&> && assignable_from<T&, const T&> && assignable_from<T&, const T>;
// [concept.semiregular]
TP<CL T>concept semiregular = copyable<T> && default_initializable<T>;
// [concept.regular]
TP<CL T>concept regular = semiregular<T> && equality_comparable<T>;
// [concept.invocable]
ST invocable_concept {
#if (defined(__clang_major__) && (defined(__apple_build_version__) ||__clang_major__ < 7))
    TP<CL F, CL... A> auto freq(F&& f, A&&... a) -> invoke_result_t<F, A...>;
#else
    TP<CL F, CL... A> auto freq(F&& f, A&&... a) -> decltype( my_invoke(FWD(f), FWD(a)...) );
#endif
};
TP<CL F, CL... A> concept invocable = requires_<invocable_concept, F, A...>;
// [concept.regularinvocable]
TP<CL F, CL... A>concept regular_invocable = invocable<F, A...>;
// [concept.predicate]
ST predicate_concept { TP<CL F, CL...A> auto freq(int)->requires_expr<
    regular_invocable<F, A...> && boolean_testable<invoke_result_t<F, A...>>>;
};
TP<CL F, CL... A> concept predicate = requires_<predicate_concept,F, A...>;
// [concept.relation]
TP<CL R, CL T, CL U>
concept relation = predicate<R, T, T> && predicate<R, U, U> && predicate<R, T, U> && predicate<R, U, T>;
// [concept.equiv]
TP<CL R, CL T, CL U> concept equivalence_relation = relation<R, T, U>;
// [concept.strictweakorder]
TP<CL R, CL T, CL U> concept strict_weak_order = relation<R, T, U>;
} // concept

inline NP utility {
TP<CL T> decay_t<T> CEXP decay_copy(T&& t) { return FWD(t); }
IC ST auto_fn { 
    TP<CL T> decay_t<T> COP ()(T&& t) const { return FWD(t); }
    TP<CL T> decay_t<T> FCOP %(T&& t, auto_fn) { return FWD(t); }
} Auto;
// [utility.move]
IC ST move_fn { 
    TP<CL T> DCLT(auto) COP ()(T&& t) const { return move(t); }
    TP<CL T> DCLT(auto) FCOP %(T&& t, move_fn) { return move(t); }
} Move;
// [utility.Ycomb]
TP<CL Fun> ST Y_combinator { Fun fun_;
	TP<CL F> Y_combinator(F&& fun): fun_(FWD(fun)) {}     
	TP<CL... A> DCLT(auto) COP ()(A&&...a) const { return fun_(*this, (A&&)a...); }
};
TP<CL T>Y_combinator(T)->Y_combinator<T>;
// [utility.scope_guard]
TP<CL F> ST scope_guard { F f; TP<CL FF>scope_guard(FF&& f) : f(FWD(f)) {} ~scope_guard() { f(); } };
TP<CL F> scope_guard(F)->scope_guard<F>;
} // utility
inline NP integer {
TP<CL T> CEXP make_unsigned_t<T> to_unsigned(T t) noexcept { return t; }
TP<CL T> CEXP make_signed_t<T> to_signed(T t) noexcept { return t; }
TP<CL T> CEXP T __rotl(T x, int s) noexcept {
    CEXP auto _Nd = numeric_limits<T>::digits;
    const int r = s % _Nd;
    if (r == 0) return x;
    else if (r > 0) return (x << r) | (x >> ((_Nd - r) % _Nd));
    else return (x >> -r) | (x << ((_Nd + r) % _Nd)); // rotr(x, -r)
}
TP<CL T> CEXP T __rotr(T x, int s) noexcept {
    CEXP auto _Nd = numeric_limits<T>::digits;
    const int r = s % _Nd;
    if (r == 0) return x;
    else if (r > 0) return (x >> r) | (x << ((_Nd - r) % _Nd));
    else return (x << -r) | (x >> ((_Nd + r) % _Nd)); // rotl(x, -r)
}
TP<CL T> CEXP int __countl_zero(T x) noexcept {
    CEXP auto _Nd = numeric_limits<T>::digits;
    if (x == 0) return _Nd;
    CEXP auto _Nd_ull = numeric_limits<unsigned long long>::digits;
    CEXP auto _Nd_ul = numeric_limits<unsigned long>::digits;
    CEXP auto _Nd_u = numeric_limits<unsigned>::digits;
    if CEXP (_Nd <= _Nd_u) {
        CEXP int diff = _Nd_u - _Nd;
        return __builtin_clz(x) - diff;
    } else if CEXP (_Nd <= _Nd_ul) {
        CEXP int diff = _Nd_ul - _Nd;
        return __builtin_clzl(x) - diff;
    } else if CEXP (_Nd <= _Nd_ull) {
        CEXP int diff = _Nd_ull - _Nd;
        return __builtin_clzll(x) - diff;
    } else { //(_Nd > _Nd_ull)
        static_assert(_Nd <= (2 * _Nd_ull), "Maximum supported integer size is 128-bit");
        unsigned long long high = x >> _Nd_ull;
        if (high != 0) {
  CEXP int diff = (2 * _Nd_ull) - _Nd;
  return __builtin_clzll(high) - diff;
        }
        CEXP auto __max_ull = numeric_limits<unsigned long long>::max();
        unsigned long long __low = x & __max_ull;
        return (_Nd - _Nd_ull) + __builtin_clzll(__low);
    }
}
TP<CL T> CEXP int __countl_one(T x) noexcept {
    if (x == numeric_limits<T>::max()) return numeric_limits<T>::digits;
    return __countl_zero<T>((T)~x);
}
TP<CL T> CEXP int __countr_zero(T x) noexcept {
    CEXP auto _Nd = numeric_limits<T>::digits;
    if (x == 0) return _Nd;
    CEXP auto _Nd_ull = numeric_limits<unsigned long long>::digits;
    CEXP auto _Nd_ul = numeric_limits<unsigned long>::digits;
    CEXP auto _Nd_u = numeric_limits<unsigned>::digits;
    if CEXP (_Nd <= _Nd_u) return __builtin_ctz(x);
    else if CEXP (_Nd <= _Nd_ul) return __builtin_ctzl(x);
    else if CEXP (_Nd <= _Nd_ull) return __builtin_ctzll(x);
    else // (_Nd > _Nd_ull)
    {
        static_assert(_Nd <= (2 * _Nd_ull), "Maximum supported integer size is 128-bit");
        CEXP auto __max_ull = numeric_limits<unsigned long long>::max();
        unsigned long long __low = x & __max_ull;
        if (__low != 0) return __builtin_ctzll(__low);
        unsigned long long high = x >> _Nd_ull;
        return __builtin_ctzll(high) + _Nd_ull;
    }
}
TP<CL T> CEXP int __countr_one(T x) noexcept {
    if (x == numeric_limits<T>::max()) return numeric_limits<T>::digits;
    return __countr_zero((T)~x);
}
TP<CL T> CEXP int __popcount(T x) noexcept {
    CEXP auto _Nd = numeric_limits<T>::digits;
    if (x == 0) return 0;
    CEXP auto _Nd_ull = numeric_limits<unsigned long long>::digits;
    CEXP auto _Nd_ul = numeric_limits<unsigned long>::digits;
    CEXP auto _Nd_u = numeric_limits<unsigned>::digits;
    if CEXP (_Nd <= _Nd_u) return __builtin_popcount(x);
    else if CEXP (_Nd <= _Nd_ul) return __builtin_popcountl(x);
    else if CEXP (_Nd <= _Nd_ull) return __builtin_popcountll(x);
    else { // (_Nd > _Nd_ull)
        static_assert(_Nd <= (2 * _Nd_ull), "Maximum supported integer size is 128-bit");
        CEXP auto __max_ull = numeric_limits<unsigned long long>::max();
        unsigned long long __low = x & __max_ull;
        unsigned long long high = x >> _Nd_ull;
        return __builtin_popcountll(__low) + __builtin_popcountll(high);
    }
}
TP<CL T> CEXP bool __has_single_bit(T x) noexcept { return __popcount(x) == 1; }
TP<CL T> CEXP T __bit_ceil(T x) noexcept {
    CEXP auto _Nd = numeric_limits<T>::digits;
    if (x == 0 || x == 1) return 1;
    auto shift_exponent = _Nd - __countl_zero((T)(x - 1u));
    using __promoted_type = decltype(x << 1);
    if CEXP (!is_same<__promoted_type, T>::value) {
        const int __extra_exp = sizeof(__promoted_type) / sizeof(T) / 2;
        shift_exponent |= (shift_exponent & _Nd) << __extra_exp;
    }
    return (T)1u << shift_exponent;
}
TP<CL T> CEXP T __bit_floor(T x) noexcept {
    CEXP auto _Nd = numeric_limits<T>::digits;
    if (x == 0) return 0;
    return (T)1u << (_Nd - __countl_zero((T)(x >> 1)));
}
TP<CL T> CEXP T __bit_width(T x) noexcept {
    CEXP auto _Nd = numeric_limits<T>::digits;
    return _Nd - __countl_zero(x);
}
TP<CL T, CL U = T> using breq = enable_if_t<is_integral_v<T>,U>;// && is_unsigned_v<T>, U>;
//[bit.cast]
TP<CL To, CL From, enable_if_t<sizeof(To)==sizeof(From),int> =0>
auto bit_cast(const From &src) noexcept { To dst; memcpy(&dst, &src, sizeof(To)); return dst; }
// [bit.rot], rotating
/// Rotate `x` to the left by `s` bits.
IC ST { TP<CL T>breq<T> COP ()(T x, int s) const noexcept { return __rotl(x, s); } } rotl;
/// Rotate `x` to the right by `s` bits.
IC ST { TP<CL T>breq<T> COP ()(T x, int s) const noexcept { return __rotr(x, s); } } rotr;
#define TMP(RET, NAME) \
IC ST { TP<CL T>breq<T, RET > COP ()(T x) const noexcept { return __##NAME (x); } } NAME;
// [bit.count], counting
TMP(int, countl_zero)   /// The number of contiguous zero bits, starting from the highest bit.
TMP(int, countl_one )   /// The number of contiguous one bits, starting from the highest bit.
TMP(int, countr_zero)   /// The number of contiguous zero bits, starting from the lowest bit.
TMP(int, countr_one )   /// The number of contiguous one bits, starting from the lowest bit.
TMP(int, popcount   )   /// The number of bits set in `x`.
// [bit.pow.two], integral powers of 2
TMP(bool, has_single_bit)   /// True if `x` is a power of two, false otherwise.
TMP(T, bit_ceil)        /// The smallest power-of-two not less than `x`.
TMP(T, bit_floor)       /// The largest power-of-two not greater than `x`.
TMP(T, bit_width)       /// The smallest integer greater than the base-2 logarithm of `x`.
#undef TMP
}
inline NP algo {
ST identity { TP<CL T> T&& COP ()(T&& t) const { return (T&&)t; }  };
TP<CL C = less<>, CL P = identity>
ST proj_cmp {
    C c; P p;
    TP<CL X, CL Y>proj_cmp(X&& x, Y&& y) : c((X&&)x), p((Y&&)y) {}
    TP<CL T, CL U>bool COP ()(T&& t, U&& u) const { return invoke(c, invoke(p, (T&&)t), invoke(p, (U&&)u)); }
};
TP<CL C, CL P> proj_cmp(C, P)->proj_cmp<C, P>;
}
NP ranges {
//[ranges.swap][ranges.invoke]
CPO swap = my_swap; CPO invoke = my_invoke;
} // ranges
inline NP ITER {
//[iterator.primitives]
//[std.iterator.tags]
ST contiguous_iterator_tag : random_access_iterator_tag {};
//[incrementable.traits]
TP <CL>ST incrementable_traits;
TP<CL T> ST with_difference_type { using difference_type = T; };
TP<CL, CL=void> ST incrementable_traits_helper {};
TP<>ST incrementable_traits_helper<void*> {};
TP<CL T> ST incrementable_traits_helper<T*>
    : conditional_t<is_object_v<T>, with_difference_type<ptrdiff_t>, __empty> {};
TP<CL I>ST incrementable_traits_helper<const I> : incrementable_traits<decay_t<I>> {};
TP<CL, CL = void>ST has_member_difference_type : false_type {};
TP<CL T>ST has_member_difference_type<T, void_t<typename T::difference_type>>: std::true_type{};
TP<CL T>CEXP bool has_member_difference_type_v=has_member_difference_type<T>::value;
TP<CL T> ST incrementable_traits_helper<T, enable_if_t<has_member_difference_type_v<T>>> 
{ using difference_type = typename T::difference_type; };
TP<CL T> ST incrementable_traits_helper< T, enable_if_t<!is_pointer<T>::value && 
    !has_member_difference_type_v<T> && integral<decltype(DCLV(const T&) - DCLV(const T&))>>>
        : with_difference_type<make_signed_t<decltype(DCLV(T) - DCLV(T))>> {};    
TP<CL T> ST incrementable_traits : incrementable_traits_helper<T> {};

TP<CL T> using iter_difference_t = typename incrementable_traits<T>::difference_type;
TP<CL I> using iter_value_t = typename iterator_traits<I>::value_type;
TP<CL T> using iter_reference_t = decltype(*DCLV(T));
TP<CL T> using iter_rvalue_reference_t = iter_reference_t<T>; // [[todo]] = decltype(ranges::iter_move(DCLV(T&)));
//[default.sentinel]
ST default_sentinel_t {}; IC default_sentinel_t default_sentinel {};
//[unreachable.sentinel]
ST unreachable_sentinel_t { //[[todo] : I is weakly_incrementable]
    TP<CL I> bool FCOP ==(I, unreachable_sentinel_t) { return false; }
    TP<CL I> bool FCOP !=(I, unreachable_sentinel_t) { return true; }
    TP<CL I> bool FCOP ==(unreachable_sentinel_t, I) { return false; }
    TP<CL I> bool FCOP !=(unreachable_sentinel_t, I) { return true; } 
};
IC unreachable_sentinel_t unreachable_sentinel {};
//[iter.concept]
TP<CL,CL=void>IC bool has_iter_tag = false;
TP<CL T>IC bool has_iter_tag<T, void_t<typename iterator_traits<T>::iterator_category>> = true;
TP<CL,CL=void>IC bool has_iter_concept = false;
TP<CL T>IC bool has_iter_concept<T, void_t<typename T::iterator_concept>> = true;
TP<CL T>CEXP auto iter_concept_impl() {
    if CEXP (is_pointer_v<T>) return contiguous_iterator_tag {};
    else if CEXP (has_iter_concept<T>) return typename T::iterator_concept {};
    else if CEXP (has_iter_tag<T>) 
    return typename iterator_traits<T>::iterator_category {};
}
TP<CL T>using iter_concept = decltype(iter_concept_impl<T>());
} // ITER
NP ranges {
using std::empty, std::begin, std::end, std::data, std::size, std::iter_swap;
TP<CL,CL=void>IC bool can_reference = false;
TP<CL I>IC bool can_reference<I,void_t<I&>> = true;
TP<CL,CL=void>IC bool deref=false;
TP<CL I>IC bool deref<I,enable_if_t<can_reference<decltype(*DCLV(I&))>>> = true;
//[iterator.concept]
//[iterator.concept.winc]
ST winc { TP<CL I>auto freq(I i)-> decltype(
    // declval<iter_reference_t<I>>(), requires_expr<signed_integral<iter_reference_t<I>>>{}, //[todo]
    requires_expr<same_as<I&,decltype(++i)>>{}, i++ 
);};
TP<CL I> concept weakly_incrementable = movable<I> && requires_<winc, I>;
//[iterator.concept.iterator]
TP<CL I> concept input_or_output_iterator = deref<I> && weakly_incrementable<I>;
//[iterator.concept.sentinel] [[todo]]
TP<CL S, CL I>concept sentinel_for=semiregular<S>&&input_or_output_iterator<I> && weakly_equality_comparable_with<S,I>;
//[iterator.concept.sizedsentinel]
ST sizesen {TP<CL S, CL I>auto freq(const I& i, const S& s)->decltype(
    requires_expr<same_as<iter_difference_t<I>,decltype(s - i)>>{}, requires_expr<same_as<iter_difference_t<I>,decltype(i - s)>>{}
);};
TP<CL S, CL I>concept sized_sentinel_for = sentinel_for<S,I> && requires_<sizesen, S, I>;
//[iterator.concept.input]
ST input_iter { TP<CL I> auto freq()->requires_expr<derived_from<iter_concept<I>,input_iterator_tag>>;};
TP<CL I>concept input_iterator=input_or_output_iterator<I>&& requires_<input_iter, I>;
TP<CL I>concept forward_iterator=input_iterator<I>&&derived_from<iter_concept<I>,forward_iterator_tag>;
TP<CL I>concept bidirectional_iterator=forward_iterator<I>&&derived_from<iter_concept<I>,bidirectional_iterator_tag>;
TP<CL I>concept random_access_iterator=bidirectional_iterator<I>&&derived_from<iter_concept<I>,random_access_iterator_tag>;
TP<CL I>concept contiguous_iterator=random_access_iterator<I>&&derived_from<iter_concept<I>,contiguous_iterator_tag>;

//[swap__]
ST indirectly_swappable_concept { TP<CL I1, typename I2> auto freq(I1& i1, I2& i2) -> decltype(
        ranges::iter_swap(i1, i1),ranges::iter_swap(i2, i2),ranges::iter_swap(i1, i2),ranges::iter_swap(i2, i1)
);};
TP<CL I1, CL I2 = I1>concept indirectly_swappable = //readable<I1> && readable<I2> &&
    requires_<indirectly_swappable_concept, I1, I2>;
//[range.iter.op.advance]
IC ST advance_fn {
    TP<CL I> I COP()(I& i, iter_difference_t<I> n) const { // I is input_or_output_iterator
        if CEXP (random_access_iterator<I>) i += n;
        else { if (n >= 0) while (n--) ++i; else if CEXP (bidirectional_iterator<I>) while (n++) --i; }
    }
    TP<CL I, CL S> void COP()(I& i, S bound) const {
        if CEXP (assignable_from<I&, S>) i = move(bound);
        else if CEXP (sized_sentinel_for<S, I>) (*this)(i, bound - i); else while (i != bound) ++i;
    }
    //[[todo]] (I& i, diff n, S bound)
} advance;
//[range.iter.op.next]
IC ST next_fn {
    TP<CL I>I COP()(I x) RET(++x)
    TP<CL I, CL...A>I COP ()(I x, A... a) const { advance(x, a...); return x; }
} next;

//[ranges.range] concepts
TP<CL T, CL = void> IC bool range_impl = false;
TP<CL T> IC bool range_impl<T, void_t<decltype(begin(DCLV(T&)), end(DCLV(T&)))>> = true;
TP<CL T> concept range = range_impl<T>;
TP<CL> IC bool enable_borrowed_range = false;
TP<CL T> concept borrowed_range = range<T> && (is_lvalue_reference_v<T> || enable_borrowed_range<remove_cvref_t<T>>);

TP<CL T> using iterator_t = decay_t<decltype(begin(DCLV(T&)))>;
TP<CL T> using sentinel_t = decay_t<decltype(end(DCLV(T&)))>;

TP<CL R> using range_size_t = decltype(/*ranges::*/size(DCLV(R&)));
TP<CL R> using range_difference_t = iter_difference_t<iterator_t<R>>;
TP<CL R> using range_value_t = iter_value_t<iterator_t<R>>;
TP<CL R> using range_reference_t = iter_reference_t<iterator_t<R>>;
TP<CL R> using range_rvalue_reference_t = iter_rvalue_reference_t<iterator_t<R>>;

//[range.sized]
TP<CL T, CL=void> IC bool sized_range_impl = false;
TP<CL T> IC bool sized_range_impl<T, void_t<decltype(/*ranges::*/size(DCLV(T&)))>> = range<T>;
TP<CL T> concept sized_range = sized_range_impl<T>;
//[range.refinements]
//[todo]output_range

ST input_range_concept {TP<CL T> auto freq() -> requires_expr<input_iterator<iterator_t<T>>>;};
TP<CL T>concept input_range = range<T> && requires_<input_range_concept, T>;
ST forward_range_concept {TP<CL T> auto freq() -> requires_expr<forward_iterator<iterator_t<T>>>;};
TP<CL T>concept forward_range = range<T> && requires_<forward_range_concept, T>;
ST bidirectional_range_concept {TP<CL T> auto freq() -> requires_expr<bidirectional_iterator<iterator_t<T>>>;};
TP<CL T>concept bidirectional_range = range<T> && requires_<bidirectional_range_concept, T>;
ST random_access_range_concept {TP<CL T> auto freq() -> requires_expr<random_access_iterator<iterator_t<T>>>;};
TP<CL T>concept random_access_range = range<T> && requires_<random_access_range_concept, T>;
ST contiguous_range_concept { TP<CL T> auto requires_(T& t) -> requires_expr<random_access_iterator<iterator_t<T>> && 
same_as<decltype(ranges::data(t)), add_pointer_t<range_reference_t<T>> > >;
};
TP<CL T>concept contiguous_range = range<T> && requires_<contiguous_range_concept, T>;
ST common_range_concept { TP<CL T> auto freq()->requires_expr<is_same_v<iterator_t<T>,sentinel_t<T>>>;};
TP<CL R>concept common_range = range<R> && requires_<common_range_concept, R>;
//[view.interface]
TP<CL D> CL view_interface {
    CEXP D& derived() noexcept { return static_cast<D&>(*this); }
    CEXP const D& derived() const noexcept { return static_cast<const D&>(*this); }
public:     using __interface = view_interface;
#define TMP(...) TP<CL DD=D, requires_expr<__VA_ARGS__> =0>
    CEXP bool empty() { return ::begin(derived()) == ::end(derived()); } // forward_range<D>
    CEXP bool empty() const { return ::begin(derived()) == ::end(derived()); } // forward_range<const D>
    explicit COP bool() { return !ranges::empty(derived()); }
    explicit COP bool() const { return !ranges::empty(derived()); }
    CEXP auto data() { return to_address(begin(derived())); } // contigious_range<D>
    CEXP auto data() const { return to_address(begin(derived())); }
    TMP(forward_range<DD> && sized_sentinel_for<sentinel_t<DD>, iterator_t<DD>>)
    CEXP auto size() { return ::end(derived()) - ::begin(derived()); }
    TMP(forward_range<const DD> && sized_sentinel_for<sentinel_t<const DD>, iterator_t<const DD>>)
    CEXP auto size() const { return ::end(derived()) - ::begin(derived()); }
    CEXP DCLT(auto) front() { return *begin(derived()); }
    CEXP DCLT(auto) front() const { return *begin(derived()); }
    CEXP DCLT(auto) back() { return *prev(end(derived())); }
    CEXP DCLT(auto) back() const { return *prev(end(derived())); }
    TP<CL R = D> DCLT(auto) COP[](range_difference_t<R> t) { return ::begin(derived())[t]; }
    TP<CL R = D> DCLT(auto) COP [](range_difference_t<R> t) const { return ::begin(derived())[t]; }
#undef TMP
};
//[range.view]
ST view_base { };
TP<CL T, CL=void> IC bool from_view_interface = false;
TP<CL T> IC bool from_view_interface<T, void_t<typename T::__interface>> = derived_from<T, typename T::__interface>;
TP<CL T> IC bool enable_view = derived_from<T, view_base> || from_view_interface<T>;
TP<CL T> concept view = range<T> && movable<T> && enable_view<T>;
//[range.definements]
TP<CL T>concept viewable_range = range<T> && ((view<remove_cvref_t<T>> && constructible_from<remove_cvref_t<T>, T>) ||
!view<remove_cvref_t<T>> && borrowed_range<T> );
//[range.utility]
//[range.utility.helper]
TP<CL V> concept simple_view = view<V> && range<const V> && 
same_as<iterator_t<V>,iterator_t<const V>> && same_as<sentinel_t<V>, sentinel_t<const V>>;
ST has_oper_arrow {TP<CL I>auto freq(I i)->decltype(i.operator->());};
TP<CL I> concept has_arrow = input_iterator<I> && (is_pointer_v<I> || requires_<has_oper_arrow, I>);
TP<CL T, CL U> concept different_from = !same_as<remove_cvref_t<T>, remove_cvref_t<U>>;
//[range.dangling]
ST dangling { dangling()noexcept=default;TP<CL...A>dangling(A&&...){} };
TP<CL T> ST box_ : optional<T> {
	using optional<T>::optional;
    TP<CL TT=T,requires_expr<!default_initializable<TT>> = 0> box_() = delete;
    TP<CL TT=T,requires_expr<default_initializable<TT>> = 0>
	CEXP box_() noexcept(is_nothrow_default_constructible_v<T>) : optional<T>{in_place} { }
	box_(const box_&) = default;
	box_(box_&&) = default;
	using optional<T>::operator=;
    TP<CL TT=T, requires_expr<!assignable_from<TT&, const T&>> = 0>
    box_& operator=(const box_& other) noexcept(is_nothrow_copy_constructible_v<T>) {
        if (this != addressof(other)) { if (other) this->emplace(*other); else this->reset(); }
        return *this;
    }
    TP<CL TT=T,requires_expr<!assignable_from<TT&, T>> = 0>
	box_& operator=(box_&& other) noexcept(is_nothrow_move_constructible_v<T>) {
        if (this != addressof(other)) { if (other) this->emplace(move(*other)); else this->reset();}
        return *this;
    }
};
TP<CL T> using copyable_box = box_<T>;
//[range.subrange]
enum CL subrange_kind { sized, unsized };
TP<CL From, CL To> concept convertible_to_non_slicing = 
    convertible_to<From, To> && !(is_pointer_v<decay_t<From>>&&is_pointer_v<decay_t<To>>&&
    different_from<remove_pointer_t<decay_t<From>>, remove_pointer_t<decay_t<To>>>);
TP<CL I, CL S, subrange_kind K= sized_sentinel_for<S,I> ? subrange_kind::sized : subrange_kind::unsized > 
CL subrange : public view_interface<subrange<I, S, K>> {
    static_assert(input_or_output_iterator<I>);
    static_assert(sentinel_for<S, I>);
    static_assert(K == subrange_kind::sized || !sized_sentinel_for<S, I>);
    static CEXP bool StoreSize = (K == subrange_kind::sized && !sized_sentinel_for<S, I>);
    using size_type = make_unsigned_t<iter_difference_t<I>>;
public:
    subrange()=default;
    TP<CL II, requires_expr<convertible_to_non_slicing<II, I> && !StoreSize> =0 > 
    CEXP subrange(II i, S s) : i(move(i)), s{s} {}
    TP<CL II, requires_expr<convertible_to_non_slicing<II, I> && K == subrange_kind::sized> =0 > 
    CEXP subrange(II i, S s, size_type n) : i(move(i)), s{s} ,sz {n} {}
    TP<CL R, requires_expr<borrowed_range<R>&&convertible_to_non_slicing<iterator_t<R>,I>&&
    convertible_to<sentinel_t<R>,S> && StoreSize> =0> CEXP subrange(R&& r) : subrange(r, ::size(r)) {}
    TP<CL R, requires_expr<borrowed_range<R>&&convertible_to_non_slicing<iterator_t<R>,I>&&
    convertible_to<sentinel_t<R>,S> && !StoreSize> =0> subrange(R&& r) :subrange(::begin(r), ::end(r)) {}
    TP<CL R, requires_expr<borrowed_range<R>&&convertible_to_non_slicing<iterator_t<R>,I>&&
    convertible_to<sentinel_t<R>,S> && K==subrange_kind::sized> =0> 
    CEXP subrange(R&& r, size_type n) :subrange(::begin(r), ::end(r), n) {}
    TP<CL II=I>CEXP auto begin()->enable_if_t<copyable<II>, I> const { return i; }
    TP<CL II=I>CEXP auto begin()->enable_if_t<!copyable<II>, I> { return move(i); }
    CEXP S end() const { return s; }
    CEXP bool empty() const { return i == s; }
    TP<auto KK=K>CEXP auto size()->enable_if_t<KK==subrange_kind::sized, size_type>  const
    { if CEXP (StoreSize) return sz; else return to_unsigned(s -i ); }
private: I i; S s; [[__no_unique_address__]] conditional_t<StoreSize, size_type, dangling> sz;
};
TP<CL I,CL S, requires_expr<sentinel_for<S,I>> =0>subrange(I, S)->subrange<I, S>;
TP<CL I,CL S, requires_expr<sentinel_for<S,I>> =0>
subrange(I, S, make_unsigned_t<iter_difference_t<I>>)->subrange<I,S,subrange_kind::sized>;
TP<CL R, requires_expr<borrowed_range<R>> = 0> subrange(R&&) -> subrange<iterator_t<R>, sentinel_t<R>, 
    (sized_range<R> || sized_sentinel_for<iterator_t<R>, sentinel_t<R>>) ? subrange_kind::sized : subrange_kind::unsized>;
TP<CL R, requires_expr<borrowed_range<R>> =0> subrange(R&&, make_signed_t<range_difference_t<R>>) ->
subrange<iterator_t<R>, sentinel_t<R>,subrange_kind::sized>;

TP<bool Const, CL T> using maybe_const = conditional_t<Const, const T, T>;
//[range.ref.view]
TP<CL R, requires_expr<range<R>&&is_object_v<R>> =0> CL ref_view :public view_interface<ref_view<R>> {
ST ref_req { static void FUN(R&); static void FUN(R&&)=delete;
    TP<CL T>auto freq()->decltype(FUN(DCLV(T)));
};
    R* r;
public:
    TP<CL T, requires_expr<different_from<T, ref_view> && convertible_to<T,R&>&& requires_<ref_req,T>> = 0>
    CEXP ref_view(T&& t) : r(addressof(static_cast<R&>(FWD(t)))) {}
    CEXP R& base() const { return *r; }
    CEXP auto begin() const { return ::begin(*r); }
    CEXP auto end() const { return ::end(*r); } 
    TP<CL RR=R,decltype(ranges::empty(*DCLV(RR)),0) = 0> CEXP bool empty() const { return ranges::empty(*r); }
    TP<CL RR=R,requires_expr<sized_range<R>> =0>CEXP auto size() const { return ::size(*r); }
    TP<CL RR=R,requires_expr</*contiguous_*/range<R>> =0>CEXP auto data() const { return ranges::data(*r); }
};
TP<CL R> ref_view(R&)->ref_view<R>;

NP views {
IC ST all_fn {
private:
    TP<CL R> auto CEXP impl(R&& r, tag<2>) const noexcept(noexcept(decay_copy(FWD(r))))
        -> requires_expr<view<R>, decltype(decay_copy(FWD(r)))> const { return decay_copy(FWD(r)); }
    TP<CL R> auto CEXP impl(R&& r, tag<1>) const noexcept(noexcept(ref_view(FWD(r))))
        -> decltype(ref_view(FWD(r))) { return ref_view(FWD(r)); }
    TP<CL R> auto CEXP impl(R&& r, tag<0>) const noexcept(noexcept(subrange(FWD(r)))) 
        -> decltype(subrange(FWD(r))) { return subrange(FWD(r)); }
public:
    TP<CL T> auto COP ()(T&& t) const noexcept(noexcept(impl(FWD(t), tag<2>{})))
        -> decltype(impl(FWD(t), tag<2>{})) { return impl(FWD(t), tag<2>{}); }
    TP<CL T> auto FCOP |(T&& t,all_fn f) noexcept(noexcept(f(FWD(t))))
        -> decltype(f(FWD(t))) { return f(FWD(t)); }
} all;
TP<CL T> using all_t = requires_expr<viewable_range<T>,decltype(all(DCLV(T)))>;
} // views

//[range.copy]
ST copy_fn {
    TP<CL I, CL S, CL O, CL P= identity>
    static O CEXP impl(I first, S last, O o, P p = {}) { for (;first != last; ++first, ++o) *o = *first; return o; }
    TP<CL R, CL O, CL P= identity>
    O COP ()(R&& r, O o, P p={}) const { return impl(begin(r), end(r), move(o), ref(p)); }
};
IC copy_fn copy;
ST fold_fn {// [[todo]] plus? ,requires
    TP<CL I, CL S, CL T, CL Op, CL P>
    static CEXP T impl(I first, S last, T init, Op op, P p) {
        // using U = remove_cvref_t<invoke_result_t<Op&, T, indirect_result_t<P&, I>>>; [todo]
        using U = T;
        if (first == last) return U(move(init));
        U accum = invoke(op, move(init), *first);
        while (++first != last) accum = invoke(op, move(accum), invoke(p, *first));
        return accum;
    
    TpReq(CL I, CL S, CL T, CL Op = plus<>, CL P = identity)(input_iterator<I> && sentinel_for<S,I>) 
    T COP ()(I first, S last, T init, Op op={}, P p={}) const 
        RET(impl(move(first), move(last), fmove(init), ref(op). ref(p)))
    TpReq(CL R, CL T, CL Op=std::plus<>, CL P = identity)(input_range<R>)
    T COP ()(R&& r, T init, Op op={}, P p= {}) const { return (*this)(::begin(r), ::end(r), move(init), ref(op), ref(p)); }
    TP<CL T, CL Op, CL P> ST fn {
        T init; Op op; P p;
        TpReq(CL I, CL S)(input_iterator<I> && sentinel_for<S,I>)
        T COP()(I first, S last) RET( impl(move(first), move(last), move(init), move(op), move(p)) )
        TpReq(CL R)(input_range<R>)
        T COP()(R&& r) RET( impl(::begin(r), ::end(r), move(init), move(op), move(p)) )
        TpReq(CL R)(input_range<R>)
        T FCOP|(R&& r, fn f) RET( impl(::begin(r), ::end(r), move(f.init), move(f.op), move(f.p)) )
    };
    TP<CL T, CL Op = plus<>, CL P = identity>
    auto COP ()(T init, Op op={}, P p = {}) const 
    { return fn<T, Op, P> { move(init), move(op), move(p) }; }
};
IC fold_fn fold;


//[range.transform.view]
TpReq(CL V, CL F)(input_range<V> && view<V> && copy_constructible<F>  && is_object_v<F> &&
    regular_invocable<F&, range_reference_t<V>> && can_reference<invoke_result_t<F&, range_reference_t<V>>>) 
ST transform_view { private:
    TP<bool> ST sentinel;
    TP<bool Const> CL iterator {
        TP<bool> friend ST sentinel;
        TP<bool> friend ST iterator;
        using Pa = maybe_const<Const, transform_view>;
        using B = maybe_const<Const, V>;   
        iterator_t<B> cur_; Pa* pa_;
        static CEXP auto iterator_concept_see_below() {
            if CEXP (random_access_range<B>) return random_access_iterator_tag {};
            else if CEXP (bidirectional_range<B>) return bidirectional_iterator_tag {};
            else if CEXP (forward_range<B>) return forward_iterator_tag {};
            else return input_iterator_tag {};
        }
    public:
        using iterator_concept  = decltype(iterator_concept_see_below());
        using iterator_category = iterator_concept; // [cxx23][fix]
        using value_type = remove_cvref_t<invoke_result_t<F&, range_reference_t<B>>>; //maybe_const<Const,F>&?[[todo]]
        using difference_type = range_difference_t<B>;
        using reference = invoke_result_t<F&, range_reference_t<B>>;
        using pointer = void;
        CEXP iterator(Pa& pa, iterator_t<B> cur) : pa_(addressof(pa)), cur_(cur) {}
        TpReq(CL I, bool C=Const)(same_as<I, iterator<!C>> && C && convertible_to<iterator_t<V>, iterator_t<B>>)
        CEXP iterator(I i) : cur_(move(i.cur_)), pa_(i.pa_) {}
        CEXP const auto& base() const & RET(cur_)
        CEXP auto base() && RET(move(cur_))
        DCLT(auto) COP *() const RET( my_invoke(*pa_->fun_, *cur_) )
        DCLT(auto) COP ++() { ++cur_; return *this; }
        auto COP ++(int) { if CEXP (forward_range<B>) Def_Suffix(++) else ++cur_; }

        LazyReq(B)(bidirectional_range<BB>) DCLT(auto) COP --() { --cur_; return *this; }
        LazyReq(B)(bidirectional_range<BB>) auto COP --(int) Def_Suffix(--)
#define TMPR LazyReq(B)(random_access_range<BB>)
        TMPR DCLT(auto) COP +=(difference_type n) { cur_ += n; return *this; }
        TMPR DCLT(auto) COP -=(difference_type n) { cur_ -= n; return *this; }
        TMPR DCLT(auto) COP [](difference_type n) const RET( *(cur_ + n) )
#define DEF(OP) bool FCOP OP (const iterator& x, const iterator& y) RET( x.cur_ OP y.cur_ )
        LazyReq(B)(equality_comparable<iterator_t<BB>>) DEF(==) LazyReq(B)(equality_comparable<iterator_t<BB>>) DEF(!=)
        TMPR DEF(<) TMPR DEF(>) TMPR DEF(<=) TMPR DEF(>=)
#undef DEF
        TMPR auto FCOP +(iterator i, difference_type n) RET(i+=n)
        TMPR auto FCOP +(difference_type n, iterator i) RET(i+n)
        TMPR auto FCOP -(iterator i, difference_type n) RET(i-=n)
        TpReq(CL I=iterator_t<B>)(sized_sentinel_for<I, I>) range_difference_t<B> 
        FCOP -(const iterator& x, const iterator& y) RET(x.cur_ - y.cur_)
        FC DCLT(auto) iter_move(const iterator& i) NOEXP( ranges::invoke(*pa_->fun_, *cur_) ) 
        { if CEXP (is_lvalue_reference_v<decltype(*i)>) return move(*i); return *i; }
        LazyReq(B)(indirectly_swappable<iterator_t<B>>) FC auto iter_swap(const iterator& x, const iterator& y) 
        NOEXP_RET( ranges::iter_swap(x.cur_, y.cur_) )
#undef TMPR
    };
    TP<bool Const> CL sentinel {
        TP<bool> friend ST sentinel;
        using Pa = maybe_const<Const, transform_view>;
        using B = maybe_const<Const, V>;
        sentinel_t<B> end_ = sentinel_t<B>();
    public:
        sentinel() = default;
        CEXP explicit sentinel(sentinel_t<B> end) : end_(move(end)) {}
        TpReq(CL S, bool C=Const)(same_as<S, sentinel<!C>> && C && convertible_to<sentinel_t<V>, sentinel_t<B>>)
        CEXP sentinel(S i) : end_(move(i.end_)){}
        CEXP sentinel_t<B> base() RET(end_) 
        bool FCOP ==(const iterator<Const>& x, const sentinel& y) RET( x.base() == y.end_ )
        bool FCOP ==(const sentinel& x, const iterator<Const>& y) RET( x.end_ == y.base() )
        bool FCOP !=(const iterator<Const>& x, const sentinel& y) RET( !(x == y) )
        bool FCOP !=(const sentinel& x, const iterator<Const>& y) RET( !(x == y) )
#define DEF LazyReq(B)(sized_sentinel_for<sentinel_t<BB>, iterator_t<BB>>) range_difference_t<B> FCOP - 
        DEF (const iterator<Const>& x, const sentinel& y) RET( x.cur_ - y.end_ )
        DEF (const sentinel& x, const iterator<Const>& y) RET( x.end_ - y.cur_ )
#undef DEF
    };
    V base_ = V();
    copyable_box<F> fun_;
  public:
    transform_view() = default;
    CEXP transform_view(V base, F fun) : base_(move(base)), fun_(move(fun)) {}
    CEXP V base() const RET(base_)
    CEXP iterator<false> begin() RET( {*this, ::begin(base_)} )
    LazyReq(V)(range<const VV> && regular_invocable<const F&, range_reference_t<const VV>>)
    CEXP iterator<true> begin() const RET({*this, ::begin(base_)})
    CEXP auto end() {
        if CEXP (common_range<V>) return iterator<false>{*this, ::end(base_)}; 
        else return sentinel<false>{::end(base_)};
    }
    LazyReq(V)(range<const VV> && regular_invocable<const F&, range_reference_t<const VV>>) CEXP auto end() const {
        if CEXP (common_range<V>) return iterator<true>{*this, ::end(base_)};
        else return sentinel<true>{::end(base_)};
    }
    LazyReq(V)(sized_range<VV>) CEXP auto size() RET(::size(base_) )
    LazyReq(V)(sized_range<const VV>)CEXP auto size() const RET(::size(base_) )
};
TP<CL R, CL F> transform_view(R&&, F) -> transform_view<views::all_t<R>, F>;
NP views {
IC ST transform_fn {
    TP<CL E, CL F> auto COP ()(E&& e, F&& f) const DCLT_RET(transform_view {FWD(e), FWD(f)})
    TP<CL F> ST fn {
        F f;
        TP<CL R> auto COP ()(R&& r) const DCLT_RET( transform_view {FWD(r), move(f)} )
        TP<CL R> auto FCOP |(R&& r, fn a) DCLT_RET( a(FWD(r)) )
    };
    TP<CL F> auto COP ()(F&& f) const { return fn<F>{FWD(f)}; }
} transform;
}
//[range.reverse.view]
TP<CL V> ST reverse_view : view_interface<reverse_view<V>> {
private:
    TP<bool X=true> using RI = enable_if_t<X, reverse_iterator<iterator_t<V>>>;
    TP<CL T> using RS = enable_if_t<sized_range<T>, range_difference_t<T>>;
public:
    CEXP explicit reverse_view(V base) : base_(move(base)) {}
    CEXP V base() const& { return base_; }
    TP<CL VV=V>RI<> CEXP begin() { return make_reverse_iterator(ranges::next(::begin(base_), ::end(base_))); }
    TP<CL VV=V>RI<range<const VV>>CEXP begin() const 
    { return make_reverse_iterator(ranges::next(::begin(base_), ::end(base_))); }
    TP<CL VV=V>RI<>CEXP end() { return make_reverse_iterator(::begin(base_)); }
    TP<CL VV=V>RI<range<const VV>>CEXP end() const { return make_reverse_iterator(::begin(base_)); }
    TP<CL VV=V>RS<VV> CEXP size() { return ::size(base_); }
    TP<CL VV=V>RS<const VV> CEXP size() const { return ::size(base_); }
private: V base_;
};
TP<CL T> reverse_view(T&&)->reverse_view<views::all_t<T>>;
NP views {
IC ST reverse_view_fn {
    TP<CL R> auto COP ()(R&& r) const RET( reverse_view {FWD(r)} )
    TP<CL R> auto FCOP |(R&&r, reverse_view_fn f) RET( f(FWD(r)) ) 
} reverse;
}
// [iota.view]
TP<CL W, CL B = unreachable_sentinel_t> CL iota_view : public view_interface<iota_view<W, B>> {
    ST S; ST I {
        using iterator_concept = random_access_iterator_tag;
        using iterator_category = random_access_iterator_tag; // [[todo : input_iterator_tag]]
        using value_type = W;
        using difference_type = make_signed_t<decltype(W() - W())>;
        using pointer = void;
        using reference = W;
        I() = default; CEXP explicit I(W v) : v(v) {}
        W COP*() const RET(v)
        DCLT(auto) COP++() { ++v; return *this; }
        I COP++(int) { auto t = *this; ++*this; return t; }
        DCLT(auto) COP--() { --v; return *this; }
        CEXP I COP--(int) Def_Suffix(--)
        DCLT(auto) COP+=(difference_type n) {
  if CEXP (is_unsigned_v<W>) n >= difference_type(0) ? v += W(n) : v -= W(-n); else v += n;
  return *this;
        }
        DCLT(auto) COP-=(difference_type n) {
  if CEXP (is_unsigned_v<W>) n >= difference_type(0) ? v -= W(n) : v += W(-n); else v -= n;
  return *this;
        }
        W COP[](difference_type n) { return W(v + n); }
#define DEF(OP) bool FCOP  OP (const I& x, const I& y) { return x.v OP y.v; }
        DEF(==) DEF(!=) DEF(<) DEF(>) DEF(<=) DEF(>=)
#undef DEF
        I FCOP +(I i, difference_type n) { return i += n; }
        I FCOP +(difference_type n, I i) { return i += n; }
        I FCOP -(I i, difference_type n) { return i -= n; }
        difference_type FCOP -(const I& x, const I& y) {
  using D = difference_type;
  if CEXP (is_integral_v<W>)
  { if CEXP (is_signed_v<W>) return D(D(x.v) - D(y.v)); else return (y.v > x.v) ? D(-D(y.v - x.v)) : D(x.v - y.v); }
  else return x.v - y.v;
        }
    private: W v; friend S;
    };
    ST S {
        S() = default;
        CEXP explicit S(B b) : b(b) {}
        bool FCOP ==(const I& x, const S& y) { return y._M_equal(x); }
        typename I::difference_type FCOP -(const I& x, const S& y) { return x.v - y.b; }
        typename I::difference_type FCOP -(const S& x, const I& y) { return -(y - x); }
    private: CEXP bool _M_equal(const I& x) const { return x.v == b; } B b;
    };
    W v; B b;
public:
    iota_view() = default;
    CEXP explicit iota_view(W v) : v(v) {}
    CEXP iota_view(type_identity_t<W> v, type_identity_t<B> b) : v(v), b(b) {}
    CEXP I begin() const { return I{v}; }
    CEXP auto end() const {
        if CEXP (is_same_v<W, B>) return I { b };
        else if CEXP (is_same_v<B, unreachable_sentinel_t>) return unreachable_sentinel;
        else return S { b };    
    }
    CEXP auto size() const {
        if CEXP (is_integral_v<W> && is_integral_v<B>)
      return v < 0 ? b < 0 ? to_unsigned(-v) - to_unsigned(-b) : to_unsigned(b) + to_unsigned(-v) : to_unsigned(b) - to_unsigned(v);
        else return to_unsigned(b - v);
    }
};
TP<CL W, CL B> iota_view(W, B) ->iota_view<W, B>;
NP views {
IC ST iota_fn {
    TP<CL T> auto COP ()(T&& e) const DCLT_RET( iota_view {FWD(e)} )
    TP<CL T, CL U> auto COP ()(T&& e, U&& f) const DCLT_RET( iota_view {FWD(e), FWD(f)} )
} iota;
}
NP views {
ST zip_fn {
    TP<CL R, CL S>
    ST Range {
        R r; S s;
        Range(R r, S s) : r((r)), s((s)) {}
        Range(Range const& o) : r((o.r)), s((o.s)) {}
        ST sentinel;    
        ST iterator {
            using iterator_category = bidirectional_iterator_tag;
            using pointer = void;
            using value_type = pair<range_value_t<R>, range_value_t<S>>;
            using reference = pair<range_reference_t<R>, range_reference_t<S>>;
            using difference_type = common_type_t<range_difference_t<R>, range_difference_t<S>>;
            iterator_t<R> r;    iterator_t<S> s;
            reference COP*() const { return { *r, *s }; }
            DCLT(auto) COP ++() { ++r; ++s; return *this; }
            iterator COP++(int) { auto r = *this; ++*this; return r; }
            DCLT(auto) COP --() { --r; --s; return *this; }
            iterator COP--(int) { auto r = *this; --*this; return r; }
            bool FCOP !=(const iterator& i, const iterator& j) { return i.r != j.r && i.s != j.s; }
            bool FCOP ==(const iterator& i, const iterator& j) { return i.r == j.r && i.s == j.s; }
            bool FCOP !=(const iterator& i, const sentinel& j) { return i.r != j.r && i.s != j.s; }
            bool FCOP ==(const iterator& i, const sentinel& j) { return i.r == j.r && i.s == j.s; }
            bool FCOP !=(const sentinel& i, const iterator& j) { return i.r != j.r && i.s != j.s; }
            bool FCOP ==(const sentinel& i, const iterator& j) { return i.r == j.r && i.s == j.s; }
        };
        ST sentinel { sentinel_t<R> r;    sentinel_t<S> s; };
        iterator begin() { return { std::begin(r), std::begin(s) }; }
        sentinel end() { return { std::end(r), std::end(s) }; }
    };    
        
TP<CL R, CL S> auto COP()(R&& r, S&& s) const { return Range<R, S> { (R&&)r, (S&&)s };}
};
IC zip_fn zip;
} // views
NP views {
IC ST enumerate_fn {
    TpReq(CL R)(range<R>) auto COP()(R&& r) const RET( zip(iota(0), FWD(r)) )
    TpReq(CL R)(range<R>) auto FCOP|(R&& r, enumerate_fn f)  RET(f(FWD(r)))
} enumerate;
} // views
TP<CL T> ST subset_view : view_interface<subset_view<T>> {
    ST iterator {
        using iterator_concept = forward_iterator_tag;
        using iterator_category = forward_iterator_tag;
        using value_type = T;
        using reference = T;
        using pointer = void;
        using difference_type = make_signed_t<decltype(T() - T())>;
        CEXP iterator(T t) noexcept : t(t), cur(t&(t-1)) {}
        DCLT(auto) COP ++() noexcept { cur = (cur - 1) & t; return *this; }
        iterator COP++(int) noexcept { auto cp = *this; ++*this; return cp; }
        T COP*() const noexcept RET(cur)
        bool FCOP==(const iterator& i, const iterator& j) noexcept { return i.cur == j.cur; }
        bool FCOP!=(const iterator& i, const iterator& j) noexcept { return i.cur != j.cur; }
        bool FCOP==(const iterator& i, default_sentinel_t) noexcept { return i.cur == i.t; }
        bool FCOP==(default_sentinel_t, const iterator& i) noexcept { return i.cur == i.t; }
        bool FCOP!=(const iterator& i, default_sentinel_t) noexcept { return i.cur != i.t; }
        bool FCOP!=(default_sentinel_t, const iterator& i) noexcept { return i.cur != i.t; }
    private:
        T t, cur;
    };
    CEXP subset_view(T t) noexcept: t(t) {}
    CEXP iterator begin() const noexcept RET( { t } )
    CEXP default_sentinel_t end() const noexcept RET({})
    auto CEXP size() const noexcept RET( to_unsigned(T{1})  << __popcount(t) )
private:
    T t;
};
NP views { // subset
IC ST subset_fn {
    TpReq(CL T)(is_integral_v<T>) auto COP()(T t) const noexcept RET( subset_view{t} )
    TpReq(CL T)(is_integral_v<T>) auto FCOP|(T t, subset_fn f) noexcept RET( f(t) )
} subset;
} // views
TP<CL T> ST decompose_view : view_interface<decompose_view<T>> {
    ST iterator {
        using iterator_category = forward_iterator_tag;
        using value_type = T;
        using reference = T;
        using pointer = void;
        using difference_type = make_signed_t<DCLT(T() - T())>;
        CEXP void satisfy() noexcept { while (x % i != 0) { if (i * i > x) { i = x; break; } ++i; } }
        CEXP iterator(T x) noexcept : i(2), x(x) { satisfy(); }
        DCLT(auto) COP ++() noexcept { x /= i; satisfy(); return *this; }
        iterator COP ++(int) noexcept { auto cp = *this; ++*this; return cp; }
        T COP*() const noexcept { return i; }
        bool FCOP==(const iterator& i, const iterator& j) noexcept { return i.x == j.x && i.i == j.i; }
        bool FCOP!=(const iterator& i, const iterator& j) noexcept { return !(i==j); }
        bool FCOP==(const iterator& i, default_sentinel_t) noexcept { return i.x == 1; }
        bool FCOP==(default_sentinel_t, const iterator& i) noexcept { return i.x == 1; }
        bool FCOP!=(const iterator& i, default_sentinel_t) noexcept { return i.x != 1; }
        bool FCOP!=(default_sentinel_t, const iterator& i) noexcept { return i.x != 1; }
    private:
        T x, i;
    };
    CEXP decompose_view(T t) noexcept: t(t) {}
    CEXP iterator begin() const noexcept { return { t };  }
    CEXP default_sentinel_t end() const noexcept { return {}; }
private: T t;
};
NP views {
ST decompose_fn { //decompose_view
    TpReq(CL T)(is_integral_v<T>) auto COP()(T t) const noexcept RET( decompose_view{t} )
    TpReq(CL T)(is_integral_v<T>) auto FCOP|(T t, decompose_fn) noexcept RET( f(t) )
};
IC decompose_fn decompose;
} // views
NP to_ { // ranges::to [P2601]
TP<CL R> ST proxy_iter {
    using value_type = range_value_t<R>;
    using pointer = value_type*;
    using iterator_category = input_iterator_tag;
    using reference = value_type&;
    using difference_type = ptrdiff_t;
};
TP<CL C, CL R, CL... A> auto IC impl(R&& r, A&&... a, tag<4>) DCLT_RET( C(FWD(r), FWD(a)...) )
TP<CL C, CL R, CL... A> auto IC impl(R&& r, A&&... a, tag<3>) DCLT_RET( C(begin(r), end(r), FWD(a)...) )

// [todo] maybe_simplify
TP<CL Ref, CL C>auto IC get_inserter(C& c, tag<1>)->DCLT(c.push_back(DCLV(Ref)), back_inserter(c)) { return back_inserter(c); }
TP<CL Ref, CL C>auto IC get_inserter(C& c, tag<0>)->DCLT(c.insert(end(c), DCLV(Ref)), inserter(c, end(c))) { return inserter(c, end(c)); }

ST can_reserve_concept { TP<CL C> auto freq(C& c, size_t n) -> decltype(
    c.reserve(n), Reqs( same_as<DCLT(c.size()),DCLT(c.max_size())> ), Reqs( same_as<DCLT(c.size()),DCLT(c.capacity())> )
);};
TP<CL C>concept can_reserve = requires_<can_reserve_concept, C>;
TP<CL C, CL R, CL... A> auto IC impl(R&& r, A&&... a, tag<1>)
->decltype(get_inserter<range_reference_t<R>>(DCLV(C&), tag<1>{}), C(FWD(a)...)) {
    auto c = C(FWD(a)...);
    if CEXP (sized_range<R> && can_reserve<C>) c.reserve(size(r));
    ranges::copy(r, get_inserter<range_reference_t<R>>(c, tag<1>{}));
    return c;
}
TP<TPP C, CL R, CL... A> using Cont = decltype(C(proxy_iter<R>(), proxy_iter<R>(), DCLV(A)...));
TP<CL C, CL R, CL... A> CEXP auto to(R&& r, A&&... a, tag<1>) DCLT_RET( impl<C>(FWD(r), FWD(a)..., tag<5>{}) )
TP<TPP C, CL R, CL... A> CEXP auto to(R&& r, A&& ...a, tag<1>) DCLT_RET( impl<Cont<C, R, A...>>(FWD(r), FWD(a)..., tag<5>{}) )
#define DEF(TMP, NAME) \
TP<TMP C, CL... A> ST NAME {  tuple<A...> params; \
    TP<CL R> auto COP ()(R&& r) const& -> decltype(to<C>(DCLV(R), DCLV(const A&)..., tag<1>{} )) \
    { return apply([&](auto&&...a) { return to<C>((R&&)r, FWD(a)..., tag<1>{}); }, params); } \
    TP<CL R> auto COP ()(R&& r) && -> decltype(to<C>(DCLV(R), DCLV(A)..., tag<1>{} )) \
    { return apply([&](auto&&...a) { return to<C>((R&&)r, FWD(a)..., tag<1>{}); }, move(params)); } \
    TpReq(CL R, CL Fn)(same_as<NAME, remove_cvref_t<Fn>>) auto FCOP|(R&& r, Fn&& f) DCLT_RET(FWD(f)(FWD(r))) \
};\
TP<TMP C, CL... A> CEXP auto to(A&&... a, tag<0>) { return NAME<C, decay_t<A>...>{ FWD(a)... }; }
DEF(CL, xfn) DEF(TPP, yfn)
#undef DEF
} // to_
TP<CL C, CL... A> CEXP auto to(A&&... a) DCLT_RET( to_::to<C>(FWD(a)..., tag<1>{}) )
TP<TPP C, CL... A> CEXP auto to(A&&... a) DCLT_RET( to_::to<C>(FWD(a)..., tag<1>{}) )
} // ranges

inline NP print {
TP<CL T> ST brackets { T left; T right; }; TP<CL T> brackets(T, T)->brackets<T>;
TP<CL T> ST delim { T del; }; TP<CL T> delim(T)->delim<T>;

TP<CL Obj, CL Bra> ST object_brackets { using _fmt = void; Obj& obj; Bra bra; };
TP<CL Obj, CL Del> ST object_delim { using _fmt = void; Obj& obj; Del del; };
TP<CL Bra, CL Del> ST brackets_delim { Bra bra; Del del; };
TP<CL Obj, CL Bra, CL Del> ST object_brackets_delim { using _fmt = void; Obj& obj; Bra bra; Del del; };

CEXP inline auto default_brackets = brackets { '[', ']' };
CEXP inline auto default_delim = delim { ',' };
CEXP inline auto et = delim { '\n' };
CEXP inline auto ebra = brackets { "", "" };

TP<CL Obj, CL BraT> object_brackets<Obj, brackets<BraT>>
operator/(Obj&& o, brackets<BraT> bra) { return { o, bra }; }
TP<CL Obj, CL DelT> object_delim<Obj, delim<DelT>>
operator/(Obj&& o, delim<DelT> del) { return { o, del }; }
TP<CL BraT, CL DelT> brackets_delim<brackets<BraT>, delim<DelT>>
operator/(brackets<BraT> bra, delim<DelT> del) { return { bra, del }; }
TP<CL Obj, CL BraT> object_brackets<Obj, brackets<BraT>> 
operator/(brackets<BraT> bra, Obj&& o) { return { o, bra }; }
TP<CL Obj, CL DelT> object_delim<Obj, delim<DelT>> 
operator/(delim<DelT> del, Obj&& o) { return { o, del }; }
TP<CL BraT, CL DelT> brackets_delim<brackets<BraT>, delim<DelT>>
operator/(delim<DelT> del, brackets<BraT> bra) { return { bra, del }; }
TP<CL Obj, CL BraT, CL DelT>  object_brackets_delim<Obj, brackets<BraT>, delim<DelT>> 
operator/(Obj&& o, brackets_delim<brackets<BraT>, delim<DelT>> bra_del) { return { o, bra_del.bra, bra_del.del }; }
TP<CL Obj, CL BraT, CL DelT>  object_brackets_delim<Obj, brackets<BraT>, delim<DelT>> 
operator/(brackets_delim<brackets<BraT>, delim<DelT>> bra_del, Obj&& o) { return { o, bra_del.bra, bra_del.del }; }
TP<CL Obj, CL BraT, CL DelT> object_brackets_delim<Obj, brackets<BraT>, delim<DelT>> 
operator/(object_brackets<Obj, brackets<BraT>> obj_bra, delim<DelT> del) { return { obj_bra.obj, obj_bra.bra, del }; }
TP<CL Obj, CL BraT, CL DelT> object_brackets_delim<Obj, brackets<BraT>, delim<DelT>> 
operator/(delim<DelT> del, object_brackets<Obj, brackets<BraT>> obj_bra) { return { obj_bra.obj, obj_bra.bra, del }; }
TP<CL Obj, CL BraT, CL DelT> object_brackets_delim<Obj, brackets<BraT>, delim<DelT>> 
operator/(object_delim<Obj, delim<DelT>> obj_del, brackets<BraT> bra) { return { obj_del.obj, bra, obj_del.del }; }
TP<CL Obj, CL BraT, CL DelT> object_brackets_delim<Obj, brackets<BraT>, delim<DelT>> 
operator/(brackets<BraT> bra, object_delim<Obj, delim<DelT>> obj_del) { return { obj_del.obj, bra, obj_del.del }; }
TP<CL R, CL T = void>
using printable_range = enable_if_t<ranges::range<R> && !is_tuple_like<R> &&
    !is_any_of<ranges::range_value_t<R>, char, wchar_t, char16_t, char32_t>, T>;
NP print_detail {
TP<CL, CL = void> IC bool has_del_impl = false;
TP<CL T> IC bool has_del_impl<T, void_t<decltype(DCLV(T&).del)>> = true;
TP<CL T> concept has_del = has_del_impl<remove_reference_t<T>>;
TP<CL, CL = void> IC bool has_bra_impl = false;
TP<CL T> IC bool has_bra_impl<T, void_t<decltype(DCLV(T&).bra)>> = true;
TP<CL T> concept has_bra = has_bra_impl<remove_reference_t<T>>;
}
TP<CL STRM, CL T> ST RAII_brackets {
    STRM& os; T data;
    RAII_brackets(STRM& os, T data) : os(os), data(data) { os << data.left; }
    ~RAII_brackets() { os << data.right; }
};
TP<CL T> DCLT(auto) _fmt(T&& t) {
    if CEXP (is_convertible_v<T, string_view>) return quoted(string_view(t));
    else if CEXP(is_same_v<decay_t<T>, char>) return quoted(string_view{ &t, 1 }, '\'');
    else return static_cast<T&&>(t);
}
TP<CL STRM, CL Delim>
CEXP STRM& put_delim(STRM& os, bool ok, Delim d) { if (!ok) os << d.del << " "; return os; }
// [print.declaration]
TP<CL Ch, CL Tr, CL R, printable_range<R, int> = 0>
basic_ostream<Ch, Tr>& operator<<(basic_ostream<Ch, Tr>& os, R&& r);
TP<CL Ch, CL Tr, CL Tuple, CL = void_t<typename tuple_size<Tuple>::type>>
basic_ostream<Ch, Tr>& operator<<(basic_ostream<Ch, Tr>& os, Tuple const& t);
TP<CL Ch, CL Tr, TPP W, CL R, CL... Rest, printable_range<R, int> = 0, 
CL = void_t<typename W<R, Rest...>::_fmt>> basic_ostream<Ch, Tr>& operator<<(basic_ostream<Ch, Tr>& os, W<R, Rest...> w);
TP<CL Ch, CL Tr, TPP W, CL Tp, CL... Rest,
    CL = void_t<typename tuple_size<remove_reference_t<Tp>>::type, typename W<Tp, Rest...>::_fmt>>
basic_ostream<Ch, Tr>& operator<<(basic_ostream<Ch, Tr>& os, W<Tp, Rest...> w);
//[print.impl]
TP<CL STRM, CL Tuple, CL Bra, CL Del, size_t... Is>
void print_tuple_impl(STRM&& os, Tuple const& t, index_sequence<Is...>, Bra bra, Del delim)
{ RAII_brackets _ { os, bra }; ((put_delim(os, Is == 0, delim) << _fmt(get<Is>(t))), ...);  }
TP<CL STRM, CL R, CL Bra, CL Del> void print_range_impl(STRM&& os, R&& r, Bra bra, Del del) 
{ RAII_brackets _ { os, bra }; size_t i = 0; for (auto&& elem : r) put_delim(os, ++i == 1, del) << _fmt(elem); }
//[print.operator<<]
TP<CL Ch, CL Tr, CL Tuple, CL>
basic_ostream<Ch, Tr>& operator<<(basic_ostream<Ch, Tr>& os, Tuple const& t) {
    using Ind = make_index_sequence<tuple_size_v<remove_reference_t<Tuple>>>;
    print_tuple_impl(os, t, Ind {}, default_brackets, default_delim); return os;
}
TP<CL Ch, CL Tr, CL R, printable_range<R, int>>
basic_ostream<Ch, Tr>& operator<<(basic_ostream<Ch, Tr>& os, R&& r) 
{ print_range_impl(os, static_cast<R&&>(r), default_brackets, default_delim); return os; }
TP<CL Ch, CL Tr, TPP W, CL R, CL... Rest, printable_range<R, int>, CL>
basic_ostream<Ch, Tr>& operator<<(basic_ostream<Ch, Tr>& os, W<R, Rest...> w) {
    using WW = W<R, Rest...>;
    auto del = [&] { if CEXP (print_detail::has_del<WW>) return w.del; else return default_delim; };
    auto bra = [&] { if CEXP (print_detail::has_bra<WW>) return w.bra; else return default_brackets; };
    print_range_impl(os, w.obj, bra(), del()); return os;
}
TP<CL Ch, CL Tr, TPP W, CL Tp, CL... Rest, CL>
basic_ostream<Ch, Tr>& operator<<(basic_ostream<Ch, Tr>& os, W<Tp, Rest...> w) {
    using WW = W<Tp, Rest...>;
    auto del = [&] { if CEXP (print_detail::has_del<WW>) return w.del; else return default_delim; };
    auto bra = [&] { if CEXP (print_detail::has_bra<WW>) return w.bra; else return default_brackets; };
    using Indices = make_index_sequence<tuple_size_v<remove_reference_t<Tp>>>;
    print_tuple_impl(os, w.obj, Indices {}, bra(), del()); return os;
}
}

inline NP safe {
static CEXP int ulp = 2;
TP<CL... T> using limits = numeric_limits<common_type_t<T...>>;
TP<CL TT, CL UU> IC bool eq(TT&& t, UU&& u) {
    using T = remove_reference_t<TT>; using U = remove_reference_t<UU>;
    if CEXP (is_integral_v<T> && is_integral_v<U>) {
        if CEXP (is_signed_v<T> == is_signed_v<U>) return t == u;
        else if CEXP (is_signed_v<T>) return t < 0 ? false : to_unsigned(t) == u;
        else return u < 0 ? false : t == to_unsigned(u);
    } else if CEXP (is_floating_point_v<U> || is_floating_point_v<T>) {
        auto const x = abs(t - u); return x <= limits<T,U>::epsilon() * ulp || x < limits<T,U>::min();
    } else return t == u;
}
TP<CL TT, CL UU> IC bool lt(TT&& t, UU&& u) {
    using T = remove_reference_t<TT>; using U = remove_reference_t<UU>;
    static_assert(is_floating_point_v<T> || is_floating_point_v<U>);
    if CEXP (is_integral_v<T> && is_integral_v<U>) {
        if CEXP (is_signed_v<T> == is_signed_v<U>)   return t < u;
        else if CEXP (is_signed_v<T>) return t < 0 ? true : to_unsigned(t) < u;
        else return u < 0 ? false : t < to_unsigned(u);
    } else if CEXP (is_floating_point_v<T> || is_floating_point_v<U>) {
        return eq(t, u) ? false : t < u;
    } else 
        return t < u;
}

TP<CL T> CL sf { 
    T v = {};
public:
    sf() = default; TP<CL U> CEXP sf(U&& x) : v(FWD(x)) {}
    COP T() const { return v; }
};
TP<CL T> sf(T)->sf<T>; inline sf<ull> COP ""_sf(ull x) { return x; }
inline sf<long double> COP ""_sf(long double x) { return x; }

TP<CL L, CL R> CEXP bool operator==(sf<L>const& l, sf<R>const& r) { return eq(L(l), R(r)); }
TP<CL L, CL R> CEXP bool operator==(L const& l, sf<R>const& r) { return eq(l, R(r)); }
TP<CL L, CL R> CEXP bool operator==(sf<L>const& l, R const& r) { return eq(L(l), r); }
TP<CL L, CL R> CEXP bool operator!=(sf<L>const& l, sf<R>const& r) { return !eq(L(l), R(r)); }
TP<CL L, CL R> CEXP bool operator!=(L const& l, sf<R>const& r) { return !eq(l, R(r)); }
TP<CL L, CL R> CEXP bool operator!=(sf<L>const& l, R const& r) { return !eq(L(l), r); }
TP<CL L, CL R> CEXP bool operator<(sf<L>const& l, sf<R>const& r) { return lt(L(l), R(r)); }
TP<CL L, CL R> CEXP bool operator<(L const& l, sf<R>const& r) { return lt(l, R(r)); }
TP<CL L, CL R> CEXP bool operator<(sf<L>const& l, R const& r) { return lt(L(l), r); }
TP<CL L, CL R> CEXP bool operator>(sf<L>const& l, sf<R>const& r) { return lt(R(r), L(l)); }
TP<CL L, CL R> CEXP bool operator>(L const& l, sf<R>const& r) { return lt(R(r), l); }
TP<CL L, CL R> CEXP bool operator>(sf<L>const& l, R const& r) { return lt(r, L(l)); }
TP<CL L, CL R> CEXP bool operator<=(sf<L>const& l, sf<R>const& r) { return !lt(R(r), L(l)); }
TP<CL L, CL R> CEXP bool operator<=(L const& l, sf<R>const& r) { return !lt(R(r), l); }
TP<CL L, CL R> CEXP bool operator<=(sf<L>const& l, R const& r) { return !lt(r, L(l)); }
TP<CL L, CL R> CEXP bool operator>=(sf<L>const& l, sf<R>const& r) { return !lt(L(l), R(r)); }
TP<CL L, CL R> CEXP bool operator>=(L const& l, sf<R>const& r) { return !lt(l, R(r)); }
TP<CL L, CL R> CEXP bool operator>=(sf<L>const& l, R const& r) { return !lt(L(l), r); }
TP<CL T>CEXP enable_if_t<is_integral_v<T>, sf<make_signed_t<T>>> operator-(sf<T> r) { return -to_signed(T(r)); }
}

inline NP numbers {
IC long MOD = 998244353;
TP<CL T>IC auto e_v = static_cast<T>(2.71828182845904523542816810799394033892895095050334930419921875);
TP<CL T>IC auto pi_v = static_cast<T>(3.14159265358979323851280895940618620443274267017841339111328125);
TP<CL T>IC auto inf_v = static_cast<T>(0x3f3f3f3f3f3f3f3fl);
IC double e = e_v<double>;
IC double pi = pi_v<double>;
IC int inf = inf_v<int>;
}

inline NP md {
TP<auto M = long(1e9 + 7)> ST B {
    using L = decltype(M); L v;
    CEXP B(L x = 0) : v(x % M) {}
    TP<CL... T> using Q = enable_if_t<(is_integral_v<T> && ...), B>;
    TP<CL I, CL = Q<I>> explicit COP I() const { return I(v); }
    COP int() const { return int(v); }
    using X=B&;
    X COP+=(B r) { v = (v + r.v) % M;return *this; }
    X COP-=(B r) { v = ((v - r.v) % M + M) % M; return *this; }
    X COP*=(B r) { v = (v * r.v) % M; return *this; }
    X COP/=(B r) { *this *= r.inv(); return *this; }
#define DEF(OP, OPE) B FCOP OP (B l, B r) { return l OPE r; } \
  TP<CL I> Q<I> FCOP OP (I l, B r) { return (B)l OPE r; } \
  TP<CL I> Q<I> FCOP OP (B l, I r) { return l OPE r; }
    DEF(+, +=) DEF(-, -=) DEF(*, *=) DEF(/, /=)
#undef DEF
    B COP+() const { return *this; }
    B COP-() const { return 0 - *this; }
    FC B inv(B x) { return x.inv(); }
    TP<CL I> Q<I> FC pow(B l, I r) { return l.pow(r); }
    CEXP B inv() const { return pow(M - 2); }
    TP<CL I> Q<I> CEXP pow(I r) const 
    { B b = *this, x = 1; while (r) { if (r & 1) x *= b; b *= b; r /= 2; } return x; }
    TP<CL L, CL R> Q<L, R> static CEXP pow(L l, R r) { return B(l).pow(r); }
    TP<CL I> Q<I> static fac(I r) {
        static unordered_map<I, B> f{{0, 1}};
        if (auto i = f.find(r); i != end(f)) return i->second;
        return f[r] = r * fac(r - 1);
    }
    TP<CL I> Q<I> static comb(I x, I y) { return fac(x) / fac(y) / fac(x - y); }
    X COP ++() { return *this += 1; }
    X COP --() { return *this -= 1; }
};
TP<auto M>using basic_mod = B<M>;  using mod = B<>;
inline mod COP ""_m(unsigned long long x) { return mod(x); }
}

inline NP unionfind {
CL UF {
    vector<int> fa, sz;
    size_t n, comp_cnt;
public:
    UF(size_t n): n(n), comp_cnt(n), fa(n), sz(n, 1) {
        iota(begin(fa), end(fa), 0);
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

inline NP utility {
NP pop_detail {
    TP<CL,CL=void> IC bool has_top = false;
    TP<CL T> IC bool has_top<T, void_t<decltype(DCLV(T).top())>> = true;
}
CEXP auto pop = [](auto& t) {
    using T = decay_t<decltype(t)>;
    auto __g = [&]()->auto&& { if CEXP (pop_detail::has_top<T>) return t.top(); else return t.front(); };
    auto ret = move(const_cast<typename T::value_type&>(__g()));    
    t.pop(); return ret;
};
} // utility

inline NP direction {
CEXP int dir [][2] { {0,1}, {1,0}, {0,-1}, {-1,0} };
CEXP int dir8[][2] { {0,1}, {1,0}, {0,-1}, {-1,0}, {1,1}, {-1,1}, {1,-1}, {-1,-1} };
CEXP auto valid = [](auto m, auto n) { return [=](size_t x, size_t y) { return x < m && y < n; }; };
}
inline NP init {
#ifdef __cpp_lib_memory_resource
IC auto set_pmr = [] {
    static byte buffer [1 << 30];
    static auto pool = pmr::monotonic_buffer_resource { data(buffer), size(buffer) };
    set_default_resource(&pool);
    return 0;
};
#endif
IC auto set_fast_io = [] { 
    ios::sync_with_stdio(false); cin.tie(nullptr); cout.tie(nullptr); cout << setprecision(12); return 0;
};
} // init
} // my
NP std {
TP<CL> concept is_vector_v = false; TP<CL T> concept is_vector_v<vector<T>> = true;
TP<CL T> ST tuple_size<vector<T>> : integral_constant<size_t, vector_size_v> {};
TP<size_t I, CL T>ST tuple_element<I, vector<T>> : enable_if<true, T> {};
TP<size_t I, CL T, requires_expr<is_vector_v<decay_t<T>>> = 0>
DCLT(auto) get(T&& t) { return FWD(t)[I]; }
} // std
inline NP simplify {
    #define Yc Y_combinator
    NP rg = ranges; NP vw = ranges::views;
    using rg::to;
    CPO fac = vw::decompose; CPO subset=vw::subset;
    CPO range=vw::iota; CPO zip=vw::zip; CPO enu=vw::enumerate; 
    CPO rev=vw::reverse; CPO tran=vw::transform;
} // simplify
