#include <bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
#define debug(...) cout << #__VA_ARGS__ << "\t" << forward_as_tuple(__VA_ARGS__)/ebra << endl;
#define ALL(...) begin(__VA_ARGS__), end(__VA_ARGS__)
#define RALL(...) rbegin(__VA_ARGS__), rend(__VA_ARGS__)
// [decompose.vector.size]
inline constexpr size_t vector_size_v = 2;

inline namespace my {
#define FWD(...) static_cast<decltype(__VA_ARGS__)&&>(__VA_ARGS__)
#define IC inline constexpr
#define concept IC bool
#define CPO constexpr inline auto
#define FC friend constexpr
#define COP constexpr operator
#define FCOP friend constexpr operator

using namespace std;
using ull = unsigned long long;
namespace pbds_detail { using namespace __gnu_pbds;
template<class T,class V=null_type,class C=less<>>using order_tree = tree<T, V, C, rb_tree_tag, tree_order_statistics_node_update>;
} // namespace pbds_detail
using pbds_detail::order_tree;
inline namespace type_traits {
struct __empty {};
template<class,class...>auto _req_impl(...)->false_type;
template<class R, class... Args,class=decltype(&R::template freq<Args...>)>auto _req_impl(int)->true_type;
template<class R, class... Args> IC bool requires_ = decltype(_req_impl<R, Args...>(0))::value;
template<bool Expr,class T=int> using requires_expr = enable_if_t<Expr, T>;
template<size_t I> struct priority_tag : priority_tag<I - 1>{}; template<>struct priority_tag<0> {};
//[remove.cvref]
template<class T>struct type_identity { using type = T;};
template<class T>using type_identity_t = typename type_identity<T>::type;
template<class T>struct remove_cvref : remove_cv<remove_reference_t<T>> {};
template<class T>using remove_cvref_t = typename remove_cvref<T>::type;
//[common.reference]
template<template<class...> class AliasT, class... Args>auto exists_helper(long) -> false_type;
template<template<class...> class AliasT, class... Args, class = AliasT<Args...>> auto exists_helper(int) -> true_type;
template<template<class...> class AliasT, class... Args>
IC bool exists_v = decltype(exists_helper<AliasT, Args...>(0))::value;
namespace common_detail { 
template<class...>struct common_type;
template<class T, class U>struct copy_cv { using type = U;};
template<class T, class U>struct copy_cv<const T, U> { using type = add_const_t<U>;};
template<class T, class U>struct copy_cv<volatile T, U> {using type = add_volatile_t<U>;};
template<class T, class U>struct copy_cv<const volatile T, U> {using type = add_cv_t<U>;};
template<class T, class U>using copy_cv_t = typename copy_cv<T, U>::type;
template<class T>using cref_t = add_lvalue_reference_t<const remove_reference_t<T>>;
template<class T, class U>using cond_res_t = decltype(false ? declval<T (&)()>()() : declval<U (&)()>()());
// For some value of "simple"
template<class A, class B, class = remove_reference_t<A>,class=remove_reference_t<B>, class = void> struct common_ref {};
template<class A, class B>using common_ref_t = typename common_ref<A, B>::type;
template<class A, class B, class=remove_reference_t<A>,class=remove_reference_t<B>, class=void> struct lval_common_ref {};
template<class A, class B, class X, class Y>
struct lval_common_ref<A, B, X, Y, enable_if_t<is_reference_v<cond_res_t<copy_cv_t<X, Y>&, copy_cv_t<Y, X>&>>>> 
{ using type = cond_res_t<copy_cv_t<X, Y>&, copy_cv_t<Y, X>&>; };
template<class A, class B> using lval_common_ref_t = typename lval_common_ref<A, B>::type;
template<class A, class B, class X, class Y> struct common_ref<A&, B&, X, Y> : lval_common_ref<A&, B&> {};
template<class X, class Y> using rref_cr_helper_t = remove_reference_t<lval_common_ref_t<X&, Y&>>&&;
template<class A, class B, class X, class Y> struct common_ref<A&&, B&&, X, Y, enable_if_t<
is_convertible_v<A&&, rref_cr_helper_t<X, Y>> &&is_convertible_v<B&&, rref_cr_helper_t<X, Y>>>>
{ using type = rref_cr_helper_t<X, Y>; };
template<class A, class B, class X, class Y> struct common_ref<A&&, B&, X, Y, enable_if_t<
    is_convertible_v<A&&, lval_common_ref_t<const X&, Y&>>>>
{ using type = lval_common_ref_t<const X&, Y&>; };
template<class A, class B, class X, class Y> struct common_ref<A&, B&&, X, Y> : common_ref<B&&, A&> {};
template<class> struct xref { template<class U> using type = U; };
template<class A> struct xref<A&> 
{ template<class U> using type = add_lvalue_reference_t<typename xref<A>::template type<U>>; };
template<class A> struct xref<A&&> 
{ template<class U> using type = add_rvalue_reference_t<typename xref<A>::template type<U>>; };
template<class A> struct xref<const A> 
{ template<class U> using type = add_const_t<typename xref<A>::template type<U>>; };
template<class A> struct xref<volatile A> 
{ template<class U> using type = add_volatile_t<typename xref<A>::template type<U>>; };
template<class A> struct xref<const volatile A> 
{ template<class U> using type = add_cv_t<typename xref<A>::template type<U>>; };
template<class T, class U, template<class> class TQual,template<class> class UQual> struct basic_common_reference {};
template<class...> struct common_reference;
template<class... Ts> using common_reference_t = typename common_reference<Ts...>::type;
template<> struct common_reference<> {};
template<class T0> struct common_reference<T0> { using type = T0; };
template<class T, class U> IC bool has_common_ref_v = exists_v<common_ref_t, T, U>;
template<class T, class U> using basic_common_ref_t = typename basic_common_reference<remove_cvref_t<T>, remove_cvref_t<U>,
            xref<T>::template type, xref<U>::template type>::type;
template<class T, class U> IC bool has_basic_common_ref_v = exists_v<basic_common_ref_t, T, U>;
template<class T, class U> IC bool has_cond_res_v = exists_v<cond_res_t, T, U>;
template<class T, class U, class = void> struct binary_common_ref : common_type<T, U> {};
template<class T, class U> struct binary_common_ref<T, U, enable_if_t<has_common_ref_v<T, U>>>: common_ref<T, U> {};
template<class T, class U> struct binary_common_ref<T, U, enable_if_t<has_basic_common_ref_v<T, U> && !has_common_ref_v<T, U>>>
{ using type = basic_common_ref_t<T, U>; };
template<class T, class U>
struct binary_common_ref<T, U, enable_if_t<has_cond_res_v<T, U> && !has_basic_common_ref_v<T, U> && !has_common_ref_v<T, U>>>
{ using type = cond_res_t<T, U>; };
template<class T1, class T2>struct common_reference<T1, T2> : binary_common_ref<T1, T2> { };
template<class Void, class T1, class T2, class... Rest> struct multiple_common_reference {};
template<class T1, typename T2, class... Rest> struct multiple_common_reference
    <void_t<common_reference_t<T1, T2>>, T1, T2, Rest...>: common_reference<common_reference_t<T1, T2>, Rest...> {};
template<class T1,class T2,class... R> struct common_reference<T1, T2, R...>: multiple_common_reference<void, T1, T2, R...> {};
// [common.type]
template<class...> struct common_type;
template<class... Ts> using common_type_t = typename common_type<Ts...>::type;
template<class T, class U>
constexpr bool same_decayed_v = is_same<T, decay_t<T>>::value && is_same<U, decay_t<U>>::value;
template<class T, class U> using ternary_return_t = decay_t<decltype(false ? declval<T>() : declval<U>())>;
template<class, typename, class=void> struct binary_common_type {};
template<class T, class U>
struct binary_common_type<T, U, enable_if_t<!same_decayed_v<T, U>>> : common_type<decay_t<T>, decay_t<U>> {};
template<class T, class U>
struct binary_common_type<T, U, enable_if_t<same_decayed_v<T, U> && exists_v<ternary_return_t, T, U>>> 
{ using type = ternary_return_t<T, U>; };
template<class T, class U>
struct binary_common_type<T, U, enable_if_t<
same_decayed_v<T, U> && !exists_v<ternary_return_t, T, U> && exists_v<cond_res_t, cref_t<T>, cref_t<U>>>> 
{ using type = decay_t<cond_res_t<cref_t<T>, cref_t<U>>>; };
template<> struct common_type<> {};
template<class T> struct common_type<T> : common_type<T, T> {};
template<class T, class U> struct common_type<T, U>: binary_common_type<T, U> {};
template<class Void, class...> struct multiple_common_type {};
template<class T1, class T2, class... R> struct multiple_common_type<void_t<common_type_t<T1, T2>>, T1, T2, R...> 
    : common_type<common_type_t<T1, T2>, R...> {};
template<class T1, class T2, class... R> struct common_type<T1, T2, R...> : multiple_common_type<void, T1, T2, R...> {};
} // namespace common_detail
using common_detail::common_reference;
using common_detail::common_reference_t;
template<class T, class... Args> concept is_any_of = ( is_same_v<T, Args> || ... );
template<class T, class = void> IC bool is_tuple_like = false;
template<class T> IC bool is_tuple_like<T, void_t<decltype(tuple_size<T> {})>> = true;
template<class T> concept tuple_like = is_tuple_like<remove_reference_t<T>>;    
}
inline namespace concepts {
//[concept.same]
template<class T, class U> concept same_as = is_same_v<T, U>;
//[concept.derived]
struct derived_from_concept 
{ template<class D, class B> auto freq()->requires_expr<is_convertible_v<const volatile D*, const volatile B*>>; };
template<class D, class B> concept derived_from = is_base_of_v<B, D> && requires_<derived_from_concept,D,B>;
// [concept.convertible]
struct convertible_to_concept 
{ template<class From, class To> auto freq(add_rvalue_reference_t<From> (&f)())->decltype(static_cast<To>(f())); };
template<class From, class To>concept convertible_to =is_convertible_v<From, To>&&requires_<convertible_to_concept, From, To>;
// [concept.commonref]
struct common_reference_with_concept {
template<class, class> static auto test(long) -> false_type;
template<class T, class U>static auto test(int) -> enable_if_t<same_as<common_reference_t<T, U>, common_reference_t<U, T>>
 &&convertible_to<T, common_reference_t<T, U>> && convertible_to<U, common_reference_t<T, U>>,true_type>;
};
template<class T, class U>concept common_reference_with=decltype(common_reference_with_concept::test<T, U>(0))::value;
// [concepts.common]
struct common_with_concept {
template<class T, class U>auto freq()->
    decltype(static_cast<common_type_t<T, U>>(declval<T>()),static_cast<common_type_t<T, U>>(declval<U>()));
template<class, class>static auto test(long) -> false_type;
template<class T, class U> static auto test(int) -> enable_if_t<
    same_as<common_type_t<T, U>, common_type_t<U, T>> && requires_<common_with_concept, T, U> &&
    common_reference_with<add_lvalue_reference_t<const T>,add_lvalue_reference_t<const U>> &&
    common_reference_with<add_lvalue_reference_t<common_type_t<T, U>>,
    common_reference_t<add_lvalue_reference_t<const T>,add_lvalue_reference_t<const U>>>, true_type>;
};
template<class T, class U>concept common_with =decltype(common_with_concept::test<T, U>(0))::value;
// [concept.arithmetic]
template<class T>concept integral = is_integral_v<T>;
template<class T>concept signed_integral = integral<T> && is_signed_v<T>;
template<class T>concept unsigned_integral = integral<T> && !signed_integral<T>;
template<class T>concept floating_point = is_floating_point_v<T>;
// [concept.assignable]
struct assignable_from_concept {
template<class LHS,class RHS>auto freq(LHS lhs, RHS&&rhs)->decltype(
    requires_expr<same_as<decltype(lhs=forward<RHS>(rhs)), LHS>>{});
    template<class, class>static auto test(long) -> false_type;
    template<class LHS, class RHS>static auto test(int) -> enable_if_t<
        is_lvalue_reference_v<LHS> &&common_reference_with<const remove_reference_t<LHS>&,const remove_reference_t<RHS>&> &&
        requires_<assignable_from_concept, LHS, RHS>, true_type>;
};
template<class LHS, class RHS>
concept assignable_from=decltype(assignable_from_concept::test<LHS, RHS>(0))::value;
// [concept.destructible]
template<class T>concept destructible = is_nothrow_destructible_v<T>;
// [concept.constructible]
template<class T, class... Args>concept constructible_from=destructible<T> && is_constructible_v<T, Args...>;
// [concept.default.init]
template<class, class = void>IC bool is_default_initializable = false;
// Thanks to Damian Jarek on Slack for this formulation
template<class T>IC bool is_default_initializable<T, void_t<decltype(::new T)>> = true;
struct default_initializable_concept {template<class T, class = decltype(T{})>auto freq() -> void;};
template<class T> concept default_initializable =
    constructible_from<T> && requires_<default_initializable_concept, T> && is_default_initializable<T>;
// [concept.moveconstructible]
template<class T>concept move_constructible = constructible_from<T, T> && convertible_to<T, T>;
// [concept.copyconstructible]
struct copy_constructible_concept {
template<class>static auto test(long) -> false_type;
template<class T>static auto test(int) -> enable_if_t<
    move_constructible<T> &&constructible_from<T, T&> && convertible_to<T&, T> && constructible_from<T, const T&>
    && convertible_to<const T&, T> && constructible_from<T, const T> && convertible_to<const T, T>, true_type>;
};
template<class T> concept copy_constructible = decltype(copy_constructible_concept::test<T>(0))::value;
// [range.swap]
namespace swap_ {
template<class T>void swap(T&, T&) = delete;
template<class T, size_t N>void swap(T (&)[N], T (&)[N]) = delete;
struct fn { private:
template<class T, class U> static constexpr auto impl(T&& t, U&& u, priority_tag<2>) noexcept(
noexcept(swap(FWD(t), FWD(u))))-> decltype(static_cast<void>(swap(FWD(t),FWD(u))))
{ (void) swap(FWD(t), FWD(u)); }
template<class T, class U, size_t N, class F = fn> static constexpr auto impl(T (&t)[N], U (&u)[N], priority_tag<1>)
noexcept(noexcept(declval<F&>()(*t, *u)))-> decltype(declval<F&>()(*t, *u))
{ for (size_t i = 0; i < N; ++i) fn::impl(t[i], u[i], priority_tag<2>{}); }
template<class T> static constexpr auto impl(T& a, T& b, priority_tag<0>) 
noexcept(is_nothrow_move_constructible<T>::value&& is_nothrow_assignable<T&, T>::value)-> enable_if_t<
move_constructible<T> && assignable_from<T&, T>> { T temp = move(a); a = move(b); b = move(temp); }
public: template<class T, class U> auto COP ()(T&& t, U&& u) const
noexcept(noexcept(fn::impl(FWD(t), FWD(u), priority_tag<2>{}))) -> decltype(fn::impl(FWD(t), FWD(u), priority_tag<2>{}))
    { return fn::impl(FWD(t), FWD(u), priority_tag<2>{}); }
};
} // end namespace swap_
IC swap_::fn my_swap;
// [concept.swappable]
struct swappable_concept { template<class T>auto freq(T& a, T& b) -> decltype(my_swap(a, b)); };
template<class T>concept swappable = requires_<swappable_concept, T>;
struct swappable_with_concept {
template<class T, class U>auto freq(T&& t, U&& u) -> decltype(
    my_swap(FWD(t), FWD(t)), my_swap(FWD(u), FWD(u)), my_swap(FWD(t), FWD(u)), my_swap(FWD(u), FWD(t)) );
template<class, class>static auto test(long) -> false_type;
template<class T, class U>static auto test(int) -> enable_if_t<
    common_reference_with<const remove_reference_t<T>&,const remove_reference_t<U>&> &&
    requires_<swappable_with_concept, T, U>,true_type>;
};
template<class T, class U> concept swappable_with =decltype(swappable_with_concept::test<T, U>(0))::value;
// [concept.boolean_testable]
template<class T>concept boolean_testable_impl = convertible_to<T, bool>;
struct boolean_testable_concept
{ template<class T>auto freq(T&& t) ->requires_expr<boolean_testable_impl<decltype(!FWD(t))>>; };
template<class T> concept boolean_testable =boolean_testable_impl<T>&&requires_<boolean_testable_concept, T>;
// [concept.equalitycomparable]
struct weakly_equality_comparable_with_concept {
template<class T, class U> auto freq(const remove_reference_t<T>& t, const remove_reference_t<U>& u)->decltype(
requires_expr<boolean_testable<decltype(t == u)>>{},requires_expr<boolean_testable<decltype(t != u)>>{},
requires_expr<boolean_testable<decltype(u == t)>>{},requires_expr<boolean_testable<decltype(u != t)>>{});
};
template<class T, class U>concept weakly_equality_comparable_with = requires_<weakly_equality_comparable_with_concept, T, U>;
template<class T>concept equality_comparable = weakly_equality_comparable_with<T, T>;
struct equality_comparable_with_concept {
template<class, class> static auto test(long) -> false_type;
template<class T, class U>static auto test(int) -> enable_if_t< equality_comparable<T> && equality_comparable<U> && 
common_reference_with<const remove_reference_t<T>&, const remove_reference_t<U>&> &&
    equality_comparable<common_reference_t<const remove_reference_t<T>&,const remove_reference_t<U>&>> &&
    weakly_equality_comparable_with<T, U>, true_type>;
};
template<class T, class U>concept equality_comparable_with =decltype(equality_comparable_with_concept::test<T, U>(0))::value;
// [concepts.totallyordered]
struct partially_ordered_with_concept {
    template<class T, class U> auto freq(const remove_reference_t<T>& t, const remove_reference_t<U>& u)->decltype(
        requires_expr<boolean_testable<decltype(t < u)>>{},requires_expr<boolean_testable<decltype(t > u)>>{},
        requires_expr<boolean_testable<decltype(t <= u)>>{},requires_expr<boolean_testable<decltype(t >= u)>>{},
        requires_expr<boolean_testable<decltype(u < t)>>{},requires_expr<boolean_testable<decltype(u > t)>>{},
        requires_expr<boolean_testable<decltype(u <= t)>>{},requires_expr<boolean_testable<decltype(u >= t)>>{});
};
template<class T, class U>concept partially_ordered_with =requires_<partially_ordered_with_concept, T, U>;
template<class T> concept totally_ordered =equality_comparable<T> && partially_ordered_with<T, T>;
struct totally_ordered_with_concept {
    template<class, class>static auto test(long)->false_type;
    template<class T, class U> static auto test(int)->enable_if_t< 
    totally_ordered<T> && totally_ordered<U> && equality_comparable_with<T, U> && 
    totally_ordered<common_reference_t<const remove_reference_t<T>&,const remove_reference_t<U>&>> &&
    partially_ordered_with<T, U>, true_type>;
};
template<class T, class U>concept totally_ordered_with =decltype(totally_ordered_with_concept::test<T, U>(0))::value;

inline namespace invoke_ {
template<class>constexpr bool is_reference_wrapper_v = false;
template<class T> constexpr bool is_reference_wrapper_v<reference_wrapper<T>> = true;
struct fn { private:
    template<class Base, class T, class Derived, class... Args> static constexpr auto
    impl(T Base::*pmf, Derived&& ref, Args&&... args) 
        noexcept(noexcept((FWD(ref).*pmf)(FWD(args)...)))
        -> enable_if_t<is_function<T>::value && is_base_of<Base, decay_t<Derived>>::value,
        decltype((FWD(ref).*pmf)(FWD(args)...))>
    { return (FWD(ref).*pmf)(FWD(args)...); }
    template<class Base, class T, class RefWrap, class... Args> static constexpr auto
    impl(T Base::*pmf, RefWrap&& ref, Args&&... args) 
    noexcept(noexcept((ref.get().*pmf)(FWD(args)...)))
        -> enable_if_t<is_function<T>::value && is_reference_wrapper_v<decay_t<RefWrap>>,
            decltype((ref.get().*pmf)(FWD(args)...))>
    { return (ref.get().*pmf)(FWD(args)...); }
    template<class Base, class T, class Pointer, class... Args> static constexpr auto
    impl(T Base::*pmf, Pointer&& ptr, Args&&... args) 
    noexcept(noexcept(((*FWD(ptr)).*pmf)(FWD(args)...)))
        -> enable_if_t<is_function<T>::value &&!is_reference_wrapper_v<decay_t<Pointer>> &&
            !is_base_of<Base, decay_t<Pointer>>::value,
        decltype(((*FWD(ptr)).*pmf)(FWD(args)...))>
    { return ((*FWD(ptr)).*pmf)(FWD(args)...); }
    template<class Base, class T, class Derived> static constexpr auto
    impl(T Base::*pmd, Derived&& ref) noexcept(noexcept(FWD(ref).*pmd))
        -> enable_if_t<!is_function<T>::value && is_base_of<Base, decay_t<Derived>>::value,
        decltype(FWD(ref).*pmd)> { return FWD(ref).*pmd; }
    template<class Base, class T, class RefWrap>
    static constexpr auto impl(T Base::*pmd, RefWrap&& ref) noexcept(noexcept(ref.get().*pmd))
        -> enable_if_t<!is_function<T>::value && is_reference_wrapper_v<decay_t<RefWrap>>,
        decltype(ref.get().*pmd)> { return ref.get().*pmd; }
    template<class Base, class T, class Pointer> static constexpr auto
    impl(T Base::*pmd, Pointer&& ptr) noexcept(noexcept((*FWD(ptr)).*pmd))
        -> enable_if_t< !is_function<T>::value && !is_reference_wrapper_v<decay_t<Pointer>> &&
                !is_base_of<Base, decay_t<Pointer>>::value,
    decltype((*FWD(ptr)).*pmd)> { return (*FWD(ptr)).*pmd; }
    template<class F, class... Args>
    static constexpr auto impl(F&& f, Args&&... args) noexcept(
        noexcept(FWD(f)(FWD(args)...)))
        -> enable_if_t< !is_member_pointer<decay_t<F>>::value, decltype(forward<F>(f)(FWD(args)...))>
    { return FWD(f)(FWD(args)...); }
public:
    template<class F, class... Args> auto COP ()(F&& f, Args&&... args) const noexcept(
        noexcept(fn::impl(FWD(f), FWD(args)...)))
        -> decltype(fn::impl(FWD(f), FWD(args)...))
    { return fn::impl(FWD(f), FWD(args)...); }
};
} // namespace invoke_

IC invoke_::fn my_invoke;
template<class Void, class, class...> struct invoke_result_helper {};
template<class F, class... Args>
struct invoke_result_helper<void_t<decltype(my_invoke(declval<F>(), declval<Args>()...))>,F, Args...> {
    using type = decltype(my_invoke(declval<F>(), declval<Args>()...));
};
template<class F, class... Args> struct invoke_result : invoke_result_helper<void, F, Args...> {};
template<class F, class... Args>using invoke_result_t = typename invoke_result<F, Args...>::type;
// [concept.movable]
template<class T> concept movable = is_object_v<T> && move_constructible<T> && assignable_from<T&, T> && swappable<T>;
// [concept.copyable]
template<class T>concept copyable = copy_constructible<T> && movable<T> &&
    assignable_from<T&, T&> && assignable_from<T&, const T&> && assignable_from<T&, const T>;
// [concept.semiregular]
template<class T>concept semiregular = copyable<T> && default_initializable<T>;
// [concept.regular]
template<class T>concept regular = semiregular<T> && equality_comparable<T>;
// [concept.invocable]
struct invocable_concept {
    // FIXME (Clang): https://bugs.llvm.org/show_bug.cgi?id=21446
#if (defined(__clang_major__) && (defined(__apple_build_version__) ||__clang_major__ < 7))
    template<class F, class... Args> auto freq(F&& f, Args&&... args) -> invoke_result_t<F, Args...>;
#else
    template<class F, class... Args> auto freq(F&& f, Args&&... args) -> decltype( my_invoke(FWD(f), FWD(args)...) );
#endif
};
template<class F, class... Args> concept invocable = requires_<invocable_concept, F, Args...>;
// [concept.regularinvocable]
template<class F, class... Args>concept regular_invocable = invocable<F, Args...>;
// [concept.predicate]
struct predicate_concept { template<class F, class...Args> auto freq(int)->requires_expr<
    regular_invocable<F, Args...> && boolean_testable<invoke_result_t<F, Args...>>>;
};
template<class F, class... Args> concept predicate = requires_<predicate_concept,F, Args...>;
// [concept.relation]
template<class R, class T, class U>
concept relation = predicate<R, T, T> && predicate<R, U, U> && predicate<R, T, U> && predicate<R, U, T>;
// [concept.equiv]
template<class R, class T, class U> concept equivalence_relation = relation<R, T, U>;
// [concept.strictweakorder]
template<class R, class T, class U> concept strict_weak_order = relation<R, T, U>;
} // namespace concept

inline namespace utility {
template<class T> decay_t<T> constexpr decay_copy(T&& t) { return FWD(t); }
IC struct auto_fn { 
    template<class T> decay_t<T> COP ()(T&& t) const { return FWD(t); }
    template<class T> decay_t<T> FCOP %(T&& t, auto_fn) { return FWD(t); }
} Auto;
// [utility.move]
IC struct move_fn { 
    template<class T> decltype(auto) COP ()(T&& t) const { return move(t); }
    template<class T> decltype(auto) FCOP %(T&& t, move_fn) { return move(t); }
} Move;
// [utility.Ycomb]
template<class Fun> struct Y_combinator { Fun fun_;
	template<class F> Y_combinator(F&& fun): fun_(FWD(fun)) {}     
	template<class... Args> decltype(auto) COP ()(Args&&...args) const { return fun_(*this, (Args&&)args...); }
};
template<class T>Y_combinator(T)->Y_combinator<T>;
// [utility.scope_guard]
template<class F> struct scope_guard { F f; template<class FF>scope_guard(FF&& f) : f(FWD(f)) {} ~scope_guard() { f(); } };
template<class F> scope_guard(F)->scope_guard<F>;
} // namespace utility
inline namespace integer {
template<class T> constexpr make_unsigned_t<T> to_unsigned(T t) noexcept { return t; }
template<class T> constexpr make_signed_t<T> to_signed(T t) noexcept { return t; }
template<class T> constexpr T __rotl(T x, int s) noexcept {
    constexpr auto _Nd = numeric_limits<T>::digits;
    const int r = s % _Nd;
    if (r == 0) return x;
    else if (r > 0) return (x << r) | (x >> ((_Nd - r) % _Nd));
    else return (x >> -r) | (x << ((_Nd + r) % _Nd)); // rotr(x, -r)
}
template<class T> constexpr T __rotr(T x, int s) noexcept {
    constexpr auto _Nd = numeric_limits<T>::digits;
    const int r = s % _Nd;
    if (r == 0) return x;
    else if (r > 0) return (x >> r) | (x << ((_Nd - r) % _Nd));
    else return (x << -r) | (x >> ((_Nd + r) % _Nd)); // rotl(x, -r)
}
template<class T> constexpr int __countl_zero(T x) noexcept {
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
template<class T> constexpr int __countl_one(T x) noexcept {
    if (x == numeric_limits<T>::max()) return numeric_limits<T>::digits;
    return __countl_zero<T>((T)~x);
}
template<class T> constexpr int __countr_zero(T x) noexcept {
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
template<class T> constexpr int __countr_one(T x) noexcept {
    if (x == numeric_limits<T>::max()) return numeric_limits<T>::digits;
    return __countr_zero((T)~x);
}
template<class T> constexpr int __popcount(T x) noexcept {
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
template<class T> constexpr bool __has_single_bit(T x) noexcept { return __popcount(x) == 1; }
template<class T> constexpr T __bit_ceil(T x) noexcept {
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
template<class T> constexpr T __bit_floor(T x) noexcept {
    constexpr auto _Nd = numeric_limits<T>::digits;
    if (x == 0) return 0;
    return (T)1u << (_Nd - __countl_zero((T)(x >> 1)));
}
template<class T> constexpr T __bit_width(T x) noexcept {
    constexpr auto _Nd = numeric_limits<T>::digits;
    return _Nd - __countl_zero(x);
}
template<class T, class U = T> using breq = enable_if_t<is_integral_v<T>,U>;// && is_unsigned_v<T>, U>;
//[bit.cast]
template<class To, class From, enable_if_t<sizeof(To)==sizeof(From),int> =0>
auto bit_cast(const From &src) noexcept { To dst; memcpy(&dst, &src, sizeof(To)); return dst; }
// [bit.rot], rotating
/// Rotate `x` to the left by `s` bits.
IC struct { template<class T>breq<T> COP ()(T x, int s) const noexcept { return __rotl(x, s); } } rotl;
/// Rotate `x` to the right by `s` bits.
IC struct { template<class T>breq<T> COP ()(T x, int s) const noexcept { return __rotr(x, s); } } rotr;
#define TMP(RET, NAME) \
IC struct { template<class T>breq<T, RET > COP ()(T x) const noexcept { return __##NAME (x); } } NAME;
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
inline namespace algo {
struct identity { template<class T> T&& operator()(T&& t) const { return (T&&)t; }  };
template<class C = less<>, class P = identity>
struct proj_cmp {
    C c; P p;
    template<class X, class Y>proj_cmp(X&& x, Y&& y) : c((X&&)x), p((Y&&)y) {}
    template<class T, class U>bool COP ()(T&& t, U&& u) const { return invoke(c, invoke(p, (T&&)t), invoke(p, (U&&)u)); }
};
template<class C, class P> proj_cmp(C, P)->proj_cmp<C, P>;
}
namespace ranges {
//[ranges.swap][ranges.invoke]
CPO swap = my_swap; CPO invoke = my_invoke;
} // namespace ranges
inline namespace ITER {
//[iterator.primitives]
//[std.iterator.tags]
struct contiguous_iterator_tag : random_access_iterator_tag {};
//[incrementable.traits]
template <class>struct incrementable_traits;
template<class T> struct with_difference_type { using difference_type = T; };
template<class, class=void> struct incrementable_traits_helper {};
template<>struct incrementable_traits_helper<void*> {};
template<class T> struct incrementable_traits_helper<T*>
    : conditional_t<is_object_v<T>, with_difference_type<ptrdiff_t>, __empty> {};
template<class I>struct incrementable_traits_helper<const I> : incrementable_traits<decay_t<I>> {};
template<class, class = void>struct has_member_difference_type : false_type {};
template<class T>struct has_member_difference_type<T, void_t<typename T::difference_type>>: std::true_type{};
template<class T>constexpr bool has_member_difference_type_v=has_member_difference_type<T>::value;
template<class T> struct incrementable_traits_helper<T, enable_if_t<has_member_difference_type_v<T>>> 
{ using difference_type = typename T::difference_type; };
template<class T> struct incrementable_traits_helper< T, enable_if_t<!is_pointer<T>::value && 
    !has_member_difference_type_v<T> && integral<decltype(declval<const T&>() - declval<const T&>())>>>
        : with_difference_type<make_signed_t<decltype(declval<T>() - declval<T>())>> {};    
template<class T> struct incrementable_traits : incrementable_traits_helper<T> {};

template<class T> using iter_difference_t = typename incrementable_traits<T>::difference_type;
template<class I> using iter_value_t = typename iterator_traits<I>::value_type;
template<class T> using iter_reference_t = decltype(*declval<T>());
template<class T> using iter_rvalue_reference_t = iter_reference_t<T>; // [[todo]] = decltype(ranges::iter_move(declval<T&>()));
//[default.sentinel]
struct default_sentinel_t {}; IC default_sentinel_t default_sentinel {};
//[unreachable.sentinel]
struct unreachable_sentinel_t { //[[todo] : I is weakly_incrementable]
    template<class I> bool FCOP ==(I, unreachable_sentinel_t) { return false; }
    template<class I> bool FCOP !=(I, unreachable_sentinel_t) { return true; }
    template<class I> bool FCOP ==(unreachable_sentinel_t, I) { return false; }
    template<class I> bool FCOP !=(unreachable_sentinel_t, I) { return true; } 
};
IC unreachable_sentinel_t unreachable_sentinel {};
//[iter.concept]
template<class,class=void>IC bool has_iter_tag = false;
template<class T>IC bool has_iter_tag<T, void_t<typename iterator_traits<T>::iterator_category>> = true;
template<class,class=void>IC bool has_iter_concept = false;
template<class T>IC bool has_iter_concept<T, void_t<typename T::iterator_concept>> = true;
template<class T>constexpr auto iter_concept_impl() {
    if constexpr (is_pointer_v<T>) return contiguous_iterator_tag {};
    else if constexpr (has_iter_concept<T>) return typename T::iterator_concept {};
    else if constexpr (has_iter_tag<T>) 
    return typename iterator_traits<T>::iterator_category {};
}
template<class T>using iter_concept = decltype(iter_concept_impl<T>());
} // namespace ITER
namespace ranges {
using std::empty, std::begin, std::end, std::data, std::size, std::iter_swap;
template<class,class=void>IC bool can_reference = false;
template<class I>IC bool can_reference<I,void_t<I&>> = true;
template<class,class=void>IC bool deref=false;
template<class I>IC bool deref<I,enable_if_t<can_reference<decltype(*declval<I&>())>>> = true;
//[iterator.concept]
//[iterator.concept.winc]
struct winc { template<class I>auto freq(I i)-> decltype(
    // declval<iter_reference_t<I>>(), requires_expr<signed_integral<iter_reference_t<I>>>{}, //[todo]
    requires_expr<same_as<I&,decltype(++i)>>{}, i++ 
);};
template<class I> concept weakly_incrementable = movable<I> && requires_<winc, I>;
//[iterator.concept.iterator]
template<class I> concept input_or_output_iterator = deref<I> && weakly_incrementable<I>;
//[iterator.concept.sentinel] [[todo]]
template<class S, class I>concept sentinel_for=semiregular<S>&&input_or_output_iterator<I> && weakly_equality_comparable_with<S,I>;
//[iterator.concept.sizedsentinel]
struct sizesen {template<class S, class I>auto freq(const I& i, const S& s)->decltype(
    requires_expr<same_as<iter_difference_t<I>,decltype(s - i)>>{}, requires_expr<same_as<iter_difference_t<I>,decltype(i - s)>>{}
);};
template<class S, class I>concept sized_sentinel_for = sentinel_for<S,I> && requires_<sizesen, S, I>;
//[iterator.concept.input]
struct input_iter { template<class I> auto freq()->requires_expr<derived_from<iter_concept<I>,input_iterator_tag>>;};
template<class I>concept input_iterator=input_or_output_iterator<I>&& requires_<input_iter, I>;
template<class I>concept forward_iterator=input_iterator<I>&&derived_from<iter_concept<I>,forward_iterator_tag>;
template<class I>concept bidirectional_iterator=forward_iterator<I>&&derived_from<iter_concept<I>,bidirectional_iterator_tag>;
template<class I>concept random_access_iterator=bidirectional_iterator<I>&&derived_from<iter_concept<I>,random_access_iterator_tag>;
template<class I>concept contiguous_iterator=random_access_iterator<I>&&derived_from<iter_concept<I>,contiguous_iterator_tag>;

//[swap__]
struct indirectly_swappable_concept { template<class I1, typename I2> auto freq(I1& i1, I2& i2) -> decltype(
        ranges::iter_swap(i1, i1),ranges::iter_swap(i2, i2),ranges::iter_swap(i1, i2),ranges::iter_swap(i2, i1)
);};
template<class I1, class I2 = I1>concept indirectly_swappable = //readable<I1> && readable<I2> &&
    requires_<indirectly_swappable_concept, I1, I2>;
//[range.iter.op.advance]
IC struct advance_fn {
    template<class I> constexpr I operator()(I& i, iter_difference_t<I> n) const { // I is input_or_output_iterator
        if constexpr (random_access_iterator<I>) i += n;
        else { if (n >= 0) while (n--) ++i; else if constexpr (bidirectional_iterator<I>) while (n++) --i; }
    }
    template<class I, class S> constexpr void operator()(I& i, S bound) const {
        if constexpr (assignable_from<I&, S>) i = move(bound);
        else if constexpr (sized_sentinel_for<S, I>) (*this)(i, bound - i); else while (i != bound) ++i;
    }
    //[[todo]] (I& i, diff n, S bound)
} advance;
//[range.iter.op.next]
IC struct next_fn {
    template<class I> constexpr I operator()(I x) { return ++x; }
    template<class I, class...A>constexpr I operator()(I x, A... a) const { advance(x, a...); return x; }
} next;

//[ranges.range] concepts
template<class T, class = void> IC bool range_impl = false;
template<class T> IC bool range_impl<T, void_t<decltype(begin(declval<T&>()), end(declval<T&>()))>> = true;
template<class T> concept range = range_impl<T>;
template<class> IC bool enable_borrowed_range = false;
template<class T> concept borrowed_range = range<T> && (is_lvalue_reference_v<T> || enable_borrowed_range<remove_cvref_t<T>>);

template<class T> using iterator_t = decay_t<decltype(begin(declval<T&>()))>;
template<class T> using sentinel_t = decay_t<decltype(end(declval<T&>()))>;

template<class R> using range_size_t = decltype(/*ranges::*/size(declval<R&>()));
template<class R> using range_difference_t = iter_difference_t<iterator_t<R>>;
template<class R> using range_value_t = iter_value_t<iterator_t<R>>;
template<class R> using range_reference_t = iter_reference_t<iterator_t<R>>;
template<class R> using range_rvalue_reference_t = iter_rvalue_reference_t<iterator_t<R>>;

//[range.sized]
template<class T, class=void> IC bool sized_range_impl = false;
template<class T> IC bool sized_range_impl<T, void_t<decltype(/*ranges::*/size(declval<T&>()))>> = range<T>;
template<class T> concept sized_range = sized_range_impl<T>;
//[range.refinements]
//[todo]output_range

struct input_range_concept {template<class T> auto freq() -> requires_expr<input_iterator<iterator_t<T>>>;};
template<class T>concept input_range = range<T> && requires_<input_range_concept, T>;
struct forward_range_concept {template<class T> auto freq() -> requires_expr<forward_iterator<iterator_t<T>>>;};
template<class T>concept forward_range = range<T> && requires_<forward_range_concept, T>;
struct bidirectional_range_concept {template<class T> auto freq() -> requires_expr<bidirectional_iterator<iterator_t<T>>>;};
template<class T>concept bidirectional_range = range<T> && requires_<bidirectional_range_concept, T>;
struct random_access_range_concept {template<class T> auto freq() -> requires_expr<random_access_iterator<iterator_t<T>>>;};
template<class T>concept random_access_range = range<T> && requires_<random_access_range_concept, T>;
struct contiguous_range_concept { template<class T> auto requires_(T& t) -> requires_expr<random_access_iterator<iterator_t<T>> && 
same_as<decltype(ranges::data(t)), add_pointer_t<range_reference_t<T>> > >;
};
template<class T>concept contiguous_range = range<T> && requires_<contiguous_range_concept, T>;
struct common_range_concept { template<class T> auto freq()->requires_expr<is_same_v<iterator_t<T>,sentinel_t<T>>>;};
template<class R>concept common_range = range<R> && requires_<common_range_concept, R>;
//[view.interface]
template<class D> class view_interface {
    constexpr D& derived() noexcept { return static_cast<D&>(*this); }
    constexpr const D& derived() const noexcept { return static_cast<const D&>(*this); }
public:     using __interface = view_interface;
#define TMP(...) template<class DD=D, requires_expr<__VA_ARGS__> =0>
    constexpr bool empty() { return ::begin(derived()) == ::end(derived()); } // forward_range<D>
    constexpr bool empty() const { return ::begin(derived()) == ::end(derived()); } // forward_range<const D>
    constexpr explicit operator bool() { return !ranges::empty(derived()); }
    constexpr explicit operator bool() const { return !ranges::empty(derived()); }
    constexpr auto data() { return to_address(begin(derived())); } // contigious_range<D>
    constexpr auto data() const { return to_address(begin(derived())); }
    TMP(forward_range<DD> && sized_sentinel_for<sentinel_t<DD>, iterator_t<DD>>)
    constexpr auto size() { return ::end(derived()) - ::begin(derived()); }
    TMP(forward_range<const DD> && sized_sentinel_for<sentinel_t<const DD>, iterator_t<const DD>>)
    constexpr auto size() const { return ::end(derived()) - ::begin(derived()); }
    constexpr decltype(auto) front() { return *begin(derived()); }
    constexpr decltype(auto) front() const { return *begin(derived()); }
    constexpr decltype(auto) back() { return *prev(end(derived())); }
    constexpr decltype(auto) back() const { return *prev(end(derived())); }
    template<class R = D> constexpr decltype(auto) operator[](range_difference_t<R> t) { return ::begin(derived())[t]; }
    template<class R = D> constexpr decltype(auto) operator[](range_difference_t<R> t) const { return ::begin(derived())[t]; }
#undef TMP
};
//[range.view]
struct view_base { };
template<class T, class=void> IC bool from_view_interface = false;
template<class T> IC bool from_view_interface<T, void_t<typename T::__interface>> = derived_from<T, typename T::__interface>;
template<class T> IC bool enable_view = derived_from<T, view_base> || from_view_interface<T>;
template<class T> concept view = range<T> && movable<T> && enable_view<T>;
//[range.definements]
template<class T>concept viewable_range = range<T> && ((view<remove_cvref_t<T>> && constructible_from<remove_cvref_t<T>, T>) ||
!view<remove_cvref_t<T>> && borrowed_range<T> );
//[range.utility]
//[range.utility.helper]
template<class V> concept simple_view = view<V> && range<const V> && 
same_as<iterator_t<V>,iterator_t<const V>> && same_as<sentinel_t<V>, sentinel_t<const V>>;
struct has_oper_arrow {template<class I>auto freq(I i)->decltype(i.operator->());};
template<class I> concept has_arrow = input_iterator<I> && (is_pointer_v<I> || requires_<has_oper_arrow, I>);
template<class T, class U> concept different_from = !same_as<remove_cvref_t<T>, remove_cvref_t<U>>;
//[range.dangling]
struct dangling { dangling()noexcept=default;template<class...A>dangling(A&&...){} };
template<class T> struct box_ : optional<T> {
	using optional<T>::optional;
    template<class TT=T,requires_expr<!default_initializable<TT>> = 0> box_() = delete;
    template<class TT=T,requires_expr<default_initializable<TT>> = 0>
	constexpr box_() noexcept(is_nothrow_default_constructible_v<T>) : optional<T>{in_place} { }
	box_(const box_&) = default;
	box_(box_&&) = default;
	using optional<T>::operator=;
    template<class TT=T, requires_expr<!assignable_from<TT&, const T&>> = 0>
    box_& operator=(const box_& other) noexcept(is_nothrow_copy_constructible_v<T>) {
        if (this != addressof(other)) { if (other) this->emplace(*other); else this->reset(); }
        return *this;
    }
    template<class TT=T,requires_expr<!assignable_from<TT&, T>> = 0>
	box_& operator=(box_&& other) noexcept(is_nothrow_move_constructible_v<T>) {
        if (this != addressof(other)) { if (other) this->emplace(move(*other)); else this->reset();}
        return *this;
    }
};
template<class T> using copyable_box = box_<T>;
//[range.subrange]
enum class subrange_kind { sized, unsized };
template<class From, class To> concept convertible_to_non_slicing = 
    convertible_to<From, To> && !(is_pointer_v<decay_t<From>>&&is_pointer_v<decay_t<To>>&&
    different_from<remove_pointer_t<decay_t<From>>, remove_pointer_t<decay_t<To>>>);
template<class I, class S, subrange_kind K= sized_sentinel_for<S,I> ? subrange_kind::sized : subrange_kind::unsized > 
class subrange : public view_interface<subrange<I, S, K>> {
    static_assert(input_or_output_iterator<I>);
    static_assert(sentinel_for<S, I>);
    static_assert(K == subrange_kind::sized || !sized_sentinel_for<S, I>);
    static constexpr bool StoreSize = (K == subrange_kind::sized && !sized_sentinel_for<S, I>);
    using size_type = make_unsigned_t<iter_difference_t<I>>;
public:
    subrange()=default;
    template<class II, requires_expr<convertible_to_non_slicing<II, I> && !StoreSize> =0 > 
    constexpr subrange(II i, S s) : i(move(i)), s{s} {}
    template<class II, requires_expr<convertible_to_non_slicing<II, I> && K == subrange_kind::sized> =0 > 
    constexpr subrange(II i, S s, size_type n) : i(move(i)), s{s} ,sz {n} {}
    template<class R, requires_expr<borrowed_range<R>&&convertible_to_non_slicing<iterator_t<R>,I>&&
    convertible_to<sentinel_t<R>,S> && StoreSize> =0> constexpr subrange(R&& r) : subrange(r, ::size(r)) {}
    template<class R, requires_expr<borrowed_range<R>&&convertible_to_non_slicing<iterator_t<R>,I>&&
    convertible_to<sentinel_t<R>,S> && !StoreSize> =0> subrange(R&& r) :subrange(::begin(r), ::end(r)) {}
    template<class R, requires_expr<borrowed_range<R>&&convertible_to_non_slicing<iterator_t<R>,I>&&
    convertible_to<sentinel_t<R>,S> && K==subrange_kind::sized> =0> 
    constexpr subrange(R&& r, size_type n) :subrange(::begin(r), ::end(r), n) {}
    template<class II=I>constexpr auto begin()->enable_if_t<copyable<II>, I> const { return i; }
    template<class II=I>constexpr auto begin()->enable_if_t<!copyable<II>, I> { return move(i); }
    constexpr S end() const { return s; }
    constexpr bool empty() const { return i == s; }
    template<auto KK=K>constexpr auto size()->enable_if_t<KK==subrange_kind::sized, size_type>  const
    { if constexpr (StoreSize) return sz; else return to_unsigned(s -i ); }
private: I i; S s; [[__no_unique_address__]] conditional_t<StoreSize, size_type, dangling> sz;
};
template<class I,class S, requires_expr<sentinel_for<S,I>> =0>subrange(I, S)->subrange<I, S>;
template<class I,class S, requires_expr<sentinel_for<S,I>> =0>
subrange(I, S, make_unsigned_t<iter_difference_t<I>>)->subrange<I,S,subrange_kind::sized>;
template<class R, requires_expr<borrowed_range<R>> = 0> subrange(R&&) -> subrange<iterator_t<R>, sentinel_t<R>, 
    (sized_range<R> || sized_sentinel_for<iterator_t<R>, sentinel_t<R>>) ? subrange_kind::sized : subrange_kind::unsized>;
template<class R, requires_expr<borrowed_range<R>> =0> subrange(R&&, make_signed_t<range_difference_t<R>>) ->
subrange<iterator_t<R>, sentinel_t<R>,subrange_kind::sized>;

template<bool Const, class T> using maybe_const = conditional_t<Const, const T, T>;
//[range.ref.view]
template<class R, requires_expr<range<R>&&is_object_v<R>> =0> class ref_view :public view_interface<ref_view<R>> {
struct ref_req { static void FUN(R&); static void FUN(R&&)=delete;
    template<class T>auto freq()->decltype(FUN(declval<T>()));
};
    R* r;
public:
    template<class T, requires_expr<different_from<T, ref_view> && convertible_to<T,R&>&& requires_<ref_req,T>> = 0>
    constexpr ref_view(T&& t) : r(addressof(static_cast<R&>(FWD(t)))) {}
    constexpr R& base() const { return *r; }
    constexpr auto begin() const { return ::begin(*r); }
    constexpr auto end() const { return ::end(*r); } 
    template<class RR=R,decltype(ranges::empty(*declval<RR>()),0) = 0> constexpr bool empty() const { return ranges::empty(*r); }
    template<class RR=R,requires_expr<sized_range<R>> =0>constexpr auto size() const { return ::size(*r); }
    template<class RR=R,requires_expr</*contiguous_*/range<R>> =0>constexpr auto data() const { return ranges::data(*r); }
};
template<class R> ref_view(R&)->ref_view<R>;

namespace views {
IC struct all_fn {
private:
    template<class R> auto constexpr impl(R&& r, priority_tag<2>) const noexcept(noexcept(decay_copy(FWD(r))))
        -> requires_expr<view<R>, decltype(decay_copy(FWD(r)))> const { return decay_copy(FWD(r)); }
    template<class R> auto constexpr impl(R&& r, priority_tag<1>) const noexcept(noexcept(ref_view(FWD(r))))
        -> decltype(ref_view(FWD(r))) { return ref_view(FWD(r)); }
    template<class R> auto constexpr impl(R&& r, priority_tag<0>) const noexcept(noexcept(subrange(FWD(r)))) 
        -> decltype(subrange(FWD(r))) { return subrange(FWD(r)); }
public:
    template<class T> auto COP ()(T&& t) const noexcept(noexcept(impl(FWD(t), priority_tag<2>{})))
        -> decltype(impl(FWD(t), priority_tag<2>{})) { return impl(FWD(t), priority_tag<2>{}); }
    template<class T> auto FCOP |(T&& t,all_fn f) noexcept(noexcept(f(FWD(t))))
        -> decltype(f(FWD(t))) { return f(FWD(t)); }
} all;
template<class T> using all_t = requires_expr<viewable_range<T>,decltype(all(declval<T>()))>;
} // namespace views

//[range.copy]
struct copy_fn {
    template<class I, class S, class O, class P= identity>
    static O constexpr impl(I first, S last, O o, P p = {}) { for (;first != last; ++first, ++o) *o = *first; return o; }
    template<class R, class O, class P= identity>
    O COP ()(R&& r, O o, P p={}) const { return impl(begin(r), end(r), move(o), ref(p)); }
};
IC copy_fn copy;
struct fold_fn {// [[todo]] plus? ,requires
    template<class I, class S, class T, class Op, class P>
    static constexpr T impl(I first, S last, T init, Op op, P p) {
        // using U = remove_cvref_t<invoke_result_t<Op&, T, indirect_result_t<P&, I>>>;
        using U = T;
        if (first == last) return U(move(init));
        U accum = invoke(op, move(init), *first);
        while (++first != last) accum = invoke(op, move(accum), invoke(p, *first));
        return accum;
    }
    template<class I, class S, class T, class Op = std::plus<>, class P = identity,
        requires_expr<input_iterator<I> && sentinel_for<S,I>> =0>
    constexpr T operator()(I first, S last, T init, Op op={}, P p={}) const 
    { return impl(move(first), move(last), move(init), ref(op). ref(p)); }
    template<class R, class T, class Op=std::plus<>, class P = identity,
        requires_expr<input_range<R>> = 0>
    constexpr T operator()(R&& r, T init, Op op={}, P p= {}) const 
    { return (*this)(::begin(r), ::end(r), move(init), ref(op), ref(p)); }
    template<class T, class Op, class P> struct fn {
        template<class I, class S, requires_expr<input_iterator<I> && sentinel_for<S,I>> =0>
        constexpr T operator()(I first, S last) 
        { return impl(move(first), move(last), move(init), move(op), move(p)); }
        template<class R, requires_expr<input_range<R>> = 0>
        constexpr T operator()(R&& r)
        { return impl(::begin(r), ::end(r), move(init), move(op), move(p)); }
        T init; Op op; P p;
        template<class R, requires_expr<input_range<R>> = 0>
        FC T operator|(R&& r, fn f) 
        { return impl(::begin(r), ::end(r), move(f.init), move(f.op), move(f.p)); }
    };
    template<class T, class Op = std::plus<>, class P = identity>
    auto COP ()(T init, Op op={}, P p = {}) const 
    { return fn<T, Op, P> { move(init), move(op), move(p) }; }
};
IC fold_fn fold;


//[range.transform.view]
template<class V, class F, requires_expr<input_range<V> && view<V> && copy_constructible<F>  && is_object_v<F> &&
             regular_invocable<F&, range_reference_t<V>> && can_reference<invoke_result_t<F&, range_reference_t<V>>>> = 0>
class transform_view : public view_interface<transform_view<V, F>> {
private:
    template<bool> struct sentinel;
    template<bool Const> class iterator {
        template<bool> friend struct sentinel;
        template<bool> friend struct iterator;
        using Parent = maybe_const<Const, transform_view>;          
        using Base = maybe_const<Const, V>;                         
        iterator_t<Base> cur_ = iterator_t<Base>();             
        Parent* parent_ = nullptr;
        static constexpr auto iterator_concept_see_below() {
            if constexpr (random_access_range<Base>) return random_access_iterator_tag {};
            else if constexpr (bidirectional_range<Base>) return bidirectional_iterator_tag {};
            else if constexpr (forward_range<Base>) return forward_iterator_tag {};
            else return input_iterator_tag {};
        }
    public:
        using iterator_concept  = decltype(iterator_concept_see_below());
        using iterator_category = iterator_concept; // [cxx23][fix]
        using value_type        = remove_cvref_t<invoke_result_t<F&, range_reference_t<Base>>>; //maybe_const<Const,F>&?[[todo]]
        using difference_type   = range_difference_t<Base>;
        using reference = invoke_result_t<F&, range_reference_t<Base>>;
        using pointer = void;
        iterator() = default;
        constexpr iterator(Parent& parent, iterator_t<Base> current) : parent_(addressof(parent)), cur_(current) {}
        template<class I, requires_expr<same_as<I, iterator<!Const>>> = 0, bool C = Const, class VV = V, 
            requires_expr<C && convertible_to<iterator_t<VV>, iterator_t<Base>>, int> = 0>
        constexpr const iterator_t<Base>& base() const & { return cur_; }
        constexpr iterator_t<Base> base() && { return move(cur_); }
        decltype(auto) COP *() const { return ranges::invoke(*parent_->fun_, *cur_); }
        decltype(auto) COP ++() { ++cur_; return *this; }
        auto COP ++(int) { if constexpr (forward_range<Base>) { auto tmp = *this; ++*this; return tmp; } else ++cur_; }
#define TMP(...) template<class B=Base, requires_expr<__VA_ARGS__> =0>
        TMP(bidirectional_range<B>) decltype(auto) COP --() { --cur_; return *this; }
        TMP(bidirectional_range<B>) auto COP --(int) { auto tmp = *this; --*this; return tmp; }
#define TMPR TMP(random_access_range<B>)
        TMPR decltype(auto) COP +=(difference_type n) { cur_ += n; return *this; }
        TMPR decltype(auto) COP -=(difference_type n) { cur_ -= n; return *this; }
        TMPR constexpr decltype(auto) operator[](difference_type n) const { return ranges::invoke(*parent_->fun_, cur_[n]); }
#define DEF(OP) bool FCOP OP (const iterator& x, const iterator& y) { return x.cur_ OP y.cur_; }
        TMP(equality_comparable<iterator_t<B>>) DEF(==) TMP(equality_comparable<iterator_t<B>>) DEF(!=)
        TMPR DEF(<) TMPR DEF(>) TMPR DEF(<=) TMPR DEF(>=)
#undef DEF
        TMPR auto FCOP +(iterator i, difference_type n) { return i+=n; }
        TMPR auto FCOP +(difference_type n, iterator i) { return i+n; }
        TMPR auto FCOP -(iterator i, difference_type n) { return i-=n; }
        template<class I=iterator_t<Base>, requires_expr<sized_sentinel_for<I, I>> = 0> range_difference_t<Base> 
        FCOP -(const iterator& x, const iterator& y) { return x.cur_ - y.cur_; }
        FC decltype(auto) iter_move(const iterator& i) noexcept(noexcept(ranges::invoke(*parent_->fun_, *cur_))) 
        { if constexpr (is_lvalue_reference_v<decltype(*i)>) return move(*i); return *i; }
        TMP(indirectly_swappable<iterator_t<B>>) FC auto iter_swap(const iterator& x, const iterator& y) 
        noexcept(noexcept(ranges::iter_swap(x.cur_, y.cur_))) { return ranges::iter_swap(x.cur_, y.cur_); }
#undef TMPR
    };
    template<bool Const> class sentinel {
        template<bool> friend struct sentinel;
        using Parent = maybe_const<Const, transform_view>;
        using Base = maybe_const<Const, V>;
        sentinel_t<Base> end_ = sentinel_t<Base>();
    public:
        sentinel() = default;
        constexpr explicit sentinel(sentinel_t<Base> end) : end_(move(end)) {}
        template<class S, requires_expr<same_as<S, sentinel<!Const>>> = 0,bool C = Const, class VV = V, 
            requires_expr<C && convertible_to<sentinel_t<VV>, sentinel_t<Base>>> = 0>
        constexpr sentinel(S i) : end_(move(i.end_)){}
        constexpr sentinel_t<Base> base() { return end_; }
        bool FCOP ==(const iterator<Const>& x, const sentinel& y) { return x.base() == y.end_; }
        bool FCOP ==(const sentinel& x, const iterator<Const>& y) { return x.end_ == y.base(); }
        bool FCOP !=(const iterator<Const>& x, const sentinel& y) { return !(x == y); }
        bool FCOP !=(const sentinel& x, const iterator<Const>& y) { return !(x == y); }
#define DEF TMP(sized_sentinel_for<sentinel_t<B>, iterator_t<B>>) range_difference_t<B> FCOP - 
        DEF (const iterator<Const>& x, const sentinel& y) { return x.cur_ - y.end_; }
        DEF (const sentinel& x, const iterator<Const>& y) { return x.end_ - y.cur_; }
#undef DEF
#undef TMP
    };
    V base_ = V();                              
    copyable_box <F> fun_;                       
  public:
    transform_view() = default;
    constexpr transform_view(V base, F fun) : base_(move(base)), fun_(move(fun)) {}
    constexpr V base() const { return base_; }
    constexpr iterator<false> begin() { return iterator<false>{*this, ::begin(base_)}; }
    template<class VV = V, requires_expr< range<const VV> && regular_invocable<const F&, range_reference_t<const VV>>> = 0>
    constexpr iterator<true> begin() const { return iterator<true>{*this, ::begin(base_)}; }
    constexpr auto end() {
        if constexpr (common_range<V>) return iterator<false>{*this, ::end(base_)}; 
        else return sentinel<false>{::end(base_)};
    }
    template<class VV = V, requires_expr<range<const VV> && regular_invocable<const F&, range_reference_t<const VV>>> = 0>
    constexpr auto end() const {
        if constexpr (common_range<V>) return iterator<true>{*this, ::end(base_)};
        else return sentinel<true>{::end(base_)};
    }
    template<class VV=V, requires_expr<sized_range<VV>> = 0> constexpr auto size() { return ::size(base_); }
    template<class VV=V, requires_expr<sized_range<const VV>> = 0> constexpr auto size() const { return ::size(base_); }
};
template<class R, class F> transform_view(R&&, F) -> transform_view<views::all_t<R>, F>;
namespace views {
struct transform_fn {
    template<class E, class F> auto COP ()(E&& e, F&& f) const 
    -> decltype(transform_view{FWD(e), FWD(f)}) { return transform_view { FWD(e), FWD(f) }; }
    template<class F> struct fn {
        F f;
        template<class R> auto COP ()(R&& r) const
            ->decltype(transform_view{ FWD(r), move(f) } ) { return transform_view { FWD(r), move(f) }; }
        template<class R> auto FCOP |(R&& r, fn a)->decltype(a(FWD(r))) { return a(FWD(r)); }
    };
    template<class F> auto COP ()(F&& f) const { return fn<F>{FWD(f)}; }
};
IC transform_fn transform;
}
//[range.reverse.view]
template<class V> struct reverse_view : view_interface<reverse_view<V>> {
private:
    template<bool X=true> using RI = enable_if_t<X, reverse_iterator<iterator_t<V>>>;
    template<class T> using RS = enable_if_t<sized_range<T>, range_difference_t<T>>;
public:
    constexpr explicit reverse_view(V base) : base_(move(base)) {}
    constexpr V base() const& { return base_; }
    template<class VV=V>RI<> constexpr begin() { return make_reverse_iterator(ranges::next(::begin(base_), ::end(base_))); }
    template<class VV=V>RI<range<const VV>>constexpr begin() const 
    { return make_reverse_iterator(ranges::next(::begin(base_), ::end(base_))); }
    template<class VV=V>RI<>constexpr end() { return make_reverse_iterator(::begin(base_)); }
    template<class VV=V>RI<range<const VV>>constexpr end() const { return make_reverse_iterator(::begin(base_)); }
    template<class VV=V>RS<VV> constexpr size() { return ::size(base_); }
    template<class VV=V>RS<const VV> constexpr size() const { return ::size(base_); }
private: V base_;
};
template<class T> reverse_view(T&&)->reverse_view<views::all_t<T>>;
namespace views {
    struct reverse_view_fn {
        template<class R> auto COP ()(R&& r) const { return reverse_view { FWD(r) }; }
        template<class R> auto FCOP |(R&&r, reverse_view_fn f) { return f(FWD(r)); } 
    };
    IC reverse_view_fn reverse;
}
// [iota.view]
template<class W, class B = unreachable_sentinel_t> class iota_view : public view_interface<iota_view<W, B>> {
    struct S; struct I {
        using iterator_concept = random_access_iterator_tag;
        using iterator_category = random_access_iterator_tag; // [[todo : input_iterator_tag]]
        using value_type = W;
        using difference_type = make_signed_t<decltype(W() - W())>;
        using pointer = void;
        using reference = W;
        I() = default; constexpr explicit I(W v) : v(v) {}
        constexpr W operator*() const { return v; }
        constexpr I& operator++() { ++v; return *this; }
        constexpr I operator++(int) { auto t = *this; ++*this; return t; }
        constexpr I& operator--() { --v; return *this; }
        constexpr I operator--(int) { auto t = *this; --*this; return t; }
        constexpr I& operator+=(difference_type n) {
            if constexpr (is_unsigned_v<W>) n >= difference_type(0) ? v += W(n) : v -= W(-n); else v += n;
            return *this;
        }
        constexpr I& operator-=(difference_type n) {
            if constexpr (is_unsigned_v<W>) n >= difference_type(0) ? v -= W(n) : v += W(-n); else v -= n;
            return *this;
        }
        constexpr W operator[](difference_type n) { return W(v + n); }
#define DEF(OP) bool FCOP  OP (const I& x, const I& y) { return x.v OP y.v; }
        DEF(==) DEF(!=) DEF(<) DEF(>) DEF(<=) DEF(>=)
#undef DEF
        I FCOP +(I i, difference_type n) { return i += n; }
        I FCOP +(difference_type n, I i) { return i += n; }
        I FCOP -(I i, difference_type n) { return i -= n; }
        difference_type FCOP -(const I& x, const I& y) {
            using D = difference_type;
            if constexpr (is_integral_v<W>)
            { if constexpr (is_signed_v<W>) return D(D(x.v) - D(y.v)); else return (y.v > x.v) ? D(-D(y.v - x.v)) : D(x.v - y.v); }
            else return x.v - y.v;
        }
    private: W v; friend S;
    };
    struct S {
        S() = default;
        constexpr explicit S(B b) : b(b) {}
        bool FCOP ==(const I& x, const S& y) { return y._M_equal(x); }
        typename I::difference_type FCOP -(const I& x, const S& y) { return x.v - y.b; }
        typename I::difference_type FCOP -(const S& x, const I& y) { return -(y - x); }
    private: constexpr bool _M_equal(const I& x) const { return x.v == b; } B b;
    };
    W v; B b;
public:
    iota_view() = default;
    constexpr explicit iota_view(W v) : v(v) {}
    constexpr iota_view(type_identity_t<W> v, type_identity_t<B> b) : v(v), b(b) {}
    constexpr I begin() const { return I{v}; }
    constexpr auto end() const {
        if constexpr (is_same_v<W, B>) return I { b };
        else if constexpr (is_same_v<B, unreachable_sentinel_t>) return unreachable_sentinel;
        else return S { b };    
    }
    constexpr auto size() const {
        if constexpr (is_integral_v<W> && is_integral_v<B>)
      return v < 0 ? b < 0 ? to_unsigned(-v) - to_unsigned(-b) : to_unsigned(b) + to_unsigned(-v) : to_unsigned(b) - to_unsigned(v);
        else return to_unsigned(b - v);
    }
};
template<class W, class B> iota_view(W, B) ->iota_view<W, B>;
namespace views {
struct iota_fn {
    template<class T> auto COP ()(T&& e) const { return iota_view { FWD(e) }; }
    template<class T, class U> auto COP ()(T&& e, U&& f) const { return iota_view { FWD(e), FWD(f) }; }
};
IC iota_fn iota;
}
namespace views {
struct zip_fn {
    template<class R, class S>
    struct Range {
        R r;
        S s;
        Range(R r, S s) : r((r)), s((s)) {}
        Range(Range const& o) : r((o.r)), s((o.s)) {}
        struct sentinel;    
        struct iterator {
            using iterator_category = bidirectional_iterator_tag;
            using pointer = void;
            using value_type = pair<range_value_t<R>, range_value_t<S>>;
            using reference = pair<range_reference_t<R>, range_reference_t<S>>;
            using difference_type = common_type_t<range_difference_t<R>, range_difference_t<S>>;
            iterator_t<R> r;    iterator_t<S> s;
            constexpr reference operator*() const { return { *r, *s }; }
            decltype(auto) COP ++() { ++r; ++s; return *this; }
            constexpr iterator operator++(int) { auto r = *this; ++*this; return r; }
            decltype(auto) COP --() { --r; --s; return *this; }
            constexpr iterator operator--(int) { auto r = *this; --*this; return r; }
            bool FCOP !=(const iterator& i, const iterator& j) { return i.r != j.r && i.s != j.s; }
            bool FCOP ==(const iterator& i, const iterator& j) { return i.r == j.r && i.s == j.s; }
            bool FCOP !=(const iterator& i, const sentinel& j) { return i.r != j.r && i.s != j.s; }
            bool FCOP ==(const iterator& i, const sentinel& j) { return i.r == j.r && i.s == j.s; }
            bool FCOP !=(const sentinel& i, const iterator& j) { return i.r != j.r && i.s != j.s; }
            bool FCOP ==(const sentinel& i, const iterator& j) { return i.r == j.r && i.s == j.s; }
        };
        struct sentinel { sentinel_t<R> r;    sentinel_t<S> s; };
        iterator begin() { return { std::begin(r), std::begin(s) }; }
        sentinel end() { return { std::end(r), std::end(s) }; }
    };    
        
template<class R, class S> auto operator()(R&& r, S&& s) const { return Range<R, S> { (R&&)r, (S&&)s };}
};
IC zip_fn zip {};
} // namespace views
namespace views {
struct enumerate_fn {
    template<class R, enable_if_t<ranges::range<R>, int> =0> auto COP ()(R&& r) const { return zip(iota(0), (R&&)r); }
    template<class R, enable_if_t<ranges::range<R>, int> =0> auto FCOP |(R&& r, enumerate_fn f) { return f(FWD(r)); }
};
IC enumerate_fn enumerate {};
} // namespace views
template<class T> struct subset_view : view_interface<subset_view<T>> {
    struct iterator {
        using iterator_concept = forward_iterator_tag;
        using iterator_category = forward_iterator_tag;
        using value_type = T;
        using reference = T;
        using pointer = void;
        using difference_type = make_signed_t<decltype(T() - T())>;
        constexpr iterator(T t) noexcept : t(t), cur(t&(t-1)) {}
        decltype(auto) COP ++() noexcept { cur = (cur - 1) & t; return *this; }
        constexpr iterator operator++(int) noexcept { auto cp = *this; ++*this; return cp; }
        constexpr T operator*() const noexcept { return cur; }
        bool FCOP==(const iterator& i, const iterator& j) noexcept { return i.cur == j.cur; }
        bool FCOP!=(const iterator& i, const iterator& j) noexcept { return i.cur != j.cur; }
        bool FCOP==(const iterator& i, default_sentinel_t) noexcept { return i.cur == i.t; }
        bool FCOP==(default_sentinel_t, const iterator& i) noexcept { return i.cur == i.t; }
        bool FCOP!=(const iterator& i, default_sentinel_t) noexcept { return i.cur != i.t; }
        bool FCOP!=(default_sentinel_t, const iterator& i) noexcept { return i.cur != i.t; }
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
    template<class T, enable_if_t<is_integral_v<T>,int> =0> auto COP ()(T t) const noexcept { return subset_view { t }; }
    template<class T, enable_if_t<is_integral_v<T>,int> =0> auto FCOP |(T t, subset_fn f) noexcept { return f(t); }
};
IC subset_fn subset {};
} // namespace views
template<class T> struct decompose_view : view_interface<decompose_view<T>> {
    struct iterator {
        using iterator_category = forward_iterator_tag;
        using value_type = T;
        using reference = T;
        using pointer = void;
        using difference_type = make_signed_t<decltype(T() - T())>;
        void satisfy() noexcept { while (x % i != 0) { if (i * i > x) { i = x; break; } ++i; } }
        constexpr iterator(T x) noexcept : i(2), x(x) { satisfy(); }
        decltype(auto) COP ++() noexcept { x /= i; satisfy(); return *this; }
        constexpr iterator operator++(int) noexcept { auto cp = *this; ++*this; return cp; }
        constexpr T operator*() const noexcept { return i; }
        bool FCOP==(const iterator& i, const iterator& j) noexcept { return i.x == j.x && i.i == j.i; }
        bool FCOP!=(const iterator& i, const iterator& j) noexcept { return !(i==j); }
        bool FCOP==(const iterator& i, default_sentinel_t) noexcept { return i.x == 1; }
        bool FCOP==(default_sentinel_t, const iterator& i) noexcept { return i.x == 1; }
        bool FCOP!=(const iterator& i, default_sentinel_t) noexcept { return i.x != 1; }
        bool FCOP!=(default_sentinel_t, const iterator& i) noexcept { return i.x != 1; }
    private:
        T x, i;
    };
    constexpr decompose_view(T t) noexcept: t(t) {}
    constexpr iterator begin() const noexcept { return { t };  }
    constexpr default_sentinel_t end() const noexcept { return {}; }
private: T t;
};
namespace views {
struct decompose_fn { //decompose_view
    template<class T, enable_if_t<is_integral_v<T>,int> =0> auto COP ()(T t) const noexcept { return decompose_view { t }; }
    template<class T, enable_if_t<is_integral_v<T>,int> =0> auto FCOP |(T t, decompose_fn f) noexcept { return f(t); }
};
IC decompose_fn decompose;
} // namespace views
namespace to_ { // ranges::to [P2601]
template<class R> struct proxy_iter {
    using value_type = range_value_t<R>;
    using pointer = value_type*;
    using iterator_category = input_iterator_tag;
    using reference = value_type&;
    using difference_type = ptrdiff_t;
};
template<class C, class R, class... Args> auto IC impl(R&& r, Args&&... args, priority_tag<4>)
->decltype(C(FWD(r), FWD(args)...)) { return C(FWD(r), FWD(args)...); }
template<class C, class R, class... Args> auto IC impl(R&& r, Args&&... args, priority_tag<3>)
->decltype(C(begin(r), end(r), FWD(args)...)) { return C(begin(r), end(r), FWD(args)...); }

template<class Ref, class C>auto IC get_inserter(C& c, priority_tag<1>)
->decltype(c.push_back(declval<Ref>()), back_inserter(c)) { return back_inserter(c); }
template<class Ref, class C>auto IC get_inserter(C& c, priority_tag<0>)
->decltype(c.insert(end(c), declval<Ref>()), inserter(c, end(c))) { return inserter(c, end(c)); }

struct can_reserve_concept { template<class C> auto freq(C& c, size_t n) -> decltype(c.reserve(n), 
    requires_expr<same_as<decltype(c.size()),decltype(c.max_size())>>{},
    requires_expr<same_as<decltype(c.size()),decltype(c.capacity())>>{} 
);};
template<class C>concept can_reserve = requires_<can_reserve_concept, C>;

template<class C, class R, class... Args> auto IC impl(R&& r, Args&&... args, priority_tag<1>)
->decltype(get_inserter<range_reference_t<R>>(declval<C&>(), priority_tag<1>{}), C(FWD(args)...)) {
    auto c = C(FWD(args)...);
    if constexpr (sized_range<R> && can_reserve<C>) c.reserve(size(r));
    ranges::copy(r, get_inserter<range_reference_t<R>>(c, priority_tag<1>{}));
    return c;
}
template<template<class...> class C, class R, class... Args>
using Cont = decltype(C(proxy_iter<R>(), proxy_iter<R>(), declval<Args>()...));

template<class C, class R, class... Args> constexpr auto to(R&& r, Args&&... args, priority_tag<1>) 
->decltype(impl<C>(FWD(r), FWD(args)..., priority_tag<4>{})) { return impl<C>(FWD(r), FWD(args)..., priority_tag<5>{}); }
template<template<class...> class C, class R, class... Args> constexpr auto to(R&& r, Args&& ...args, priority_tag<0>)
 -> Cont<C, R, Args...> { return impl<Cont<C, R, Args...>>(FWD(r), FWD(args)..., priority_tag<5>{}); }

template<class C, class... Args> struct fn { tuple<Args...> params;
template<class R> auto COP ()(R&& r) const& -> decltype(impl<C>(declval<R>(), declval<const Args&>()..., priority_tag<5>{} ))
{ return apply([&r, this](auto&&...args) { return impl<C>((R&&)r, FWD(args)..., priority_tag<5>{}); }, params); }
template<class R> auto COP ()(R&& r) && -> decltype(impl<C>(declval<R>(), declval<Args>()..., priority_tag<5>{} ))
{ return apply([&r, this](auto&&...args) { return impl<C>((R&&)r, FWD(args)..., priority_tag<5>{}); }, move(params)); }
template<class R,class Fn, requires_expr<same_as<fn, remove_cvref_t<Fn>>> = 0>
auto FCOP | (R&& r, Fn&& f) -> decltype(FWD(f)(FWD(r))) { return FWD(f)(FWD(r)); }
};
template<class C, class... Args> constexpr auto to(Args&&... args, priority_tag<0>) { return fn<C, decay_t<Args>...>{ FWD(args)... }; }
template<template<class...> class C, class... Args> struct fn1 { tuple<Args...> params;
template<class R> auto COP ()(R&& r) const& -> decltype(to<C>(declval<R>(), declval<const Args&>()..., priority_tag<1>{} ))
{ return apply([&r, this](auto&&...args) { return to<C>((R&&)r, FWD(args)..., priority_tag<1>{}); }, params); }
template<class R> auto COP ()(R&& r) && -> decltype(to<C>(declval<R>(), declval<Args>()..., priority_tag<1>{} ))
{ return apply([&r, this](auto&&...args) { return to<C>((R&&)r, FWD(args)..., priority_tag<1>{}); }, move(params)); }
template<class R,class Fn, requires_expr<same_as<fn1, remove_cvref_t<Fn>>> = 0>
auto FCOP | (R&& r, Fn&& f) -> decltype(FWD(f)(FWD(r))) { return FWD(f)(FWD(r)); }
};
template<template<class...> class C, class... Args> constexpr auto to(Args&& ...args, priority_tag<0>)
{ return fn1<C, decay_t<Args>...> { FWD(args)... }; }
} // namespace to_
template<class C, class... Args> constexpr auto to(Args&&... args) 
->decltype(to_::to<C>(FWD(args)..., priority_tag<1>{})) { return to_::to<C>(FWD(args)..., priority_tag<1>{}); }
template<template<class...>class C, class... Args> constexpr auto to(Args&&... args) 
->decltype(to_::to<C>(FWD(args)..., priority_tag<1>{})) { return to_::to<C>(FWD(args)..., priority_tag<1>{}); }
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
template<class, class = void> IC bool has_del_impl = false;
template<class T> IC bool has_del_impl<T, void_t<decltype(declval<T&>().del)>> = true;
template<class T> concept has_del = has_del_impl<remove_reference_t<T>>;
template<class, class = void> IC bool has_bra_impl = false;
template<class T> IC bool has_bra_impl<T, void_t<decltype(declval<T&>().bra)>> = true;
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
template<class STRM, class Tuple, class Bra, class Del, size_t... Is>
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
template<class TT, class UU> IC bool eq(TT&& t, UU&& u) {
    using T = remove_reference_t<TT>; using U = remove_reference_t<UU>;
    if constexpr (is_integral_v<T> && is_integral_v<U>) {
        if constexpr (is_signed_v<T> == is_signed_v<U>) return t == u;
        else if constexpr (is_signed_v<T>) return t < 0 ? false : to_unsigned(t) == u;
        else return u < 0 ? false : t == to_unsigned(u);
    } else if constexpr (is_floating_point_v<U> || is_floating_point_v<T>) {
        auto const x = abs(t - u); return x <= limits<T,U>::epsilon() * ulp || x < limits<T,U>::min();
    } else return t == u;
}
template<class TT, class UU> IC bool lt(TT&& t, UU&& u) {
    using T = remove_reference_t<TT>; using U = remove_reference_t<UU>;
    static_assert(is_floating_point_v<T> || is_floating_point_v<U>);
    if constexpr (is_integral_v<T> && is_integral_v<U>) {
        if constexpr (is_signed_v<T> == is_signed_v<U>)   return t < u;
        else if constexpr (is_signed_v<T>)                     return t < 0 ? true : to_unsigned(t) < u;
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
    COP T() const { return v; }
};
template<class T> sf(T)->sf<T>; IC sf<ull> operator""_sf(ull x) { return x; }
IC sf<long double> operator""_sf(long double x) { return x; }

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
IC long MOD = 998244353;
template<class T>IC auto e_v = static_cast<T>(2.71828182845904523542816810799394033892895095050334930419921875);
template<class T>IC auto pi_v = static_cast<T>(3.14159265358979323851280895940618620443274267017841339111328125);
template<class T>IC auto inf_v = static_cast<T>(0x3f3f3f3f3f3f3f3fl);
IC double e = e_v<double>;
IC double pi = pi_v<double>;
IC int inf = inf_v<int>;
}

inline namespace md {
template<auto M = long(1e9 + 7)> struct B {
    using L = decltype(M); L v;
    constexpr B(L x = 0) : v(x % M) {}
    template<class... T> using Q = enable_if_t<(is_integral_v<T> && ...), B>;
    template<class I, class = Q<I>> explicit COP I() const { return I(v); }
    COP int() const { return int(v); }
    using X=B&;
    X COP+=(B r) { v = (v + r.v) % M;return *this; }
    X COP-=(B r) { v = ((v - r.v) % M + M) % M; return *this; }
    X COP*=(B r) { v = (v * r.v) % M; return *this; }
    X COP/=(B r) { *this *= r.inv(); return *this; }
#define DEF(OP, OPE) B FCOP OP (B l, B r) { return l OPE r; } \
            template<class I> Q<I> FCOP OP (I l, B r) { return (B)l OPE r; } \
            template<class I> Q<I> FCOP OP (B l, I r) { return l OPE r; }
    DEF(+, +=) DEF(-, -=) DEF(*, *=) DEF(/, /=)
#undef DEF
    B COP+() const { return *this; }
    B COP-() const { return 0 - *this; }
    FC B inv(B x) { return x.inv(); }
    template<class I> Q<I> FC pow(B l, I r) { return l.pow(r); }
    constexpr B inv() const { return pow(M - 2); }
    template<class I> Q<I> constexpr pow(I r) const 
    { B b = *this, x = 1; while (r) { if (r & 1) x *= b; b *= b; r /= 2; } return x; }
    template<class L, class R> Q<L, R> static constexpr pow(L l, R r) { return B(l).pow(r); }
    template<class I> Q<I> static fac(I r) {
        static unordered_map<I, B> f{{0, 1}};
        if (auto i = f.find(r); i != end(f)) return i->second;
        return f[r] = r * fac(r - 1);
    }
    template<class I> Q<I> static comb(I x, I y) { return fac(x) / fac(y) / fac(x - y); }
    X COP ++() { return *this += 1; }
    X COP --() { return *this -= 1; }
};
template<auto M>using basic_mod = B<M>;  using mod = B<>;
inline mod COP ""_m(unsigned long long x) { return mod(x); }
}

inline namespace unionfind {
class UF {
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

inline namespace utility {
namespace pop_detail {
    template<class,class=void> IC bool has_top = false;
    template<class T> IC bool has_top<T, void_t<decltype(declval<T>().top())>> = true;
}
constexpr auto pop = [](auto& t) {
    using T = decay_t<decltype(t)>;
    auto __g = [&]()->auto&& { if constexpr (pop_detail::has_top<T>) return t.top(); else return t.front(); };
    auto ret = move(const_cast<typename T::value_type&>(__g()));    
    t.pop(); return ret;
};
} // namespace utility

inline namespace direction {
constexpr int dir [][2] { {0,1}, {1,0}, {0,-1}, {-1,0} };
constexpr int dir8[][2] { {0,1}, {1,0}, {0,-1}, {-1,0}, {1,1}, {-1,1}, {1,-1}, {-1,-1} };
constexpr auto valid = [](auto m, auto n) { return [=](size_t x, size_t y) { return x < m && y < n; }; };
}
inline namespace init {
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
    #define Yc Y_combinator
    namespace rg = ranges; namespace vw = ranges::views;
    CPO fac = vw::decompose; CPO subset=vw::subset;
    CPO range=vw::iota; CPO zip=vw::zip; CPO enu=vw::enumerate; 
    CPO rev=vw::reverse; CPO tran=vw::transform; 
} // namespace simplify
