#include <bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
inline constexpr size_t vector_size_v=2;
#define NP namespace
NP std{
inline NP my{
#define debug(...) cout << #__VA_ARGS__ << "\t" << forward_as_tuple(__VA_ARGS__)/ebra << endl;
#define ALL(...) begin(__VA_ARGS__),end(__VA_ARGS__)
#define RALL(...) rbegin(__VA_ARGS__),rend(__VA_ARGS__)
#define FWD(...) static_cast<decltype(__VA_ARGS__)&&>(__VA_ARGS__)
#define DCLV(...) declval<__VA_ARGS__>()
#define NOEXP(...) noexcept(noexcept(__VA_ARGS__))
#define DCLT(...) decltype(__VA_ARGS__)
#define RET(...) {return __VA_ARGS__ ;}
#define NOEXP_RET(...) NOEXP(__VA_ARGS__) RET(__VA_ARGS__)
#define NOEXP_DCLT(...) NOEXP(__VA_ARGS__)->DCLT(__VA_ARGS__)
#define DCLT_RET(...)->DCLT(__VA_ARGS__) RET(__VA_ARGS__)
#define NOEXP_DCLT_RET(...) NOEXP(__VA_ARGS__) DCLT_RET(__VA_ARGS__)
#define CL class
#define ST struct
#define TP template
#define TY typename
#define TPP TP<CL...>CL
#define BL bool
#define CEXP constexpr
#define IC inline CEXP
#define FC friend
#define VC void CEXP
#define BC BL CEXP
#define COP CEXP operator
#define FCOP friend CEXP operator

#define CPO CEXP inline auto
#define concept IC BL
#define Rg ranges::
#define Vw views::

#define Req(...) requires_expr<__VA_ARGS__>
#define ReqExpr(...) boolT<1,decltype(__VA_ARGS__)>
#define ReqType(...) boolT<1,__VA_ARGS__>
#define TpReqt(...) Req(__VA_ARGS__)=0>
#define TpReq(...) TP< __VA_ARGS__ ,TpReqt

#define LazyT(T,...) TP<CL t=T,Req(boolT<1,t>&&(__VA_ARGS__))=0>
#define LazyV(V,...) TP<auto v=V,Req(boolV<1,v>&&(__VA_ARGS__))=0>

#define Reqs(...) Req(__VA_ARGS__) {},
#define ImplRetReq(...) __VA_ARGS__ )>>{},
#define RetReq0(ConceptName) requires_expr< ConceptName<decltype( ImplRetReq
#define RetReq(ConceptName,...) requires_expr< ConceptName<__VA_ARGS__,decltype( ImplRetReq

#define CpDef(NAME,...) ST NAME##_concept { TP<__VA_ARGS__>auto freq ImplCpDef0
#define ImplCpDef0(...) (__VA_ARGS__)->decltype ImplCpDef1
#define ImplCpDef1(...) (__VA_ARGS__  void()); }

#define CpBl(NAME,...) ST NAME##_concept { TP<__VA_ARGS__>auto freq()->ImplCpBl0
#define ImplCpBl0(...) Req(__VA_ARGS__); }
#define Creq Reqs
#define ImplCret(...) ,##__VA_ARGS__>>{},
#define Cret(Na,...) requires_expr<Na<DCLT(__VA_ARGS__) ImplCret
#define CpRef(NAME,...) requires_<NAME##_concept,__VA_ARGS__>

#define RET_THIS(...) { __VA_ARGS__ return*this;}
#define DefSuffix(OP) {auto a=*this;OP*this;return a;}
#define Crefp(T)(const T&i,const T&j)
using NP std;
using ull=unsigned long long;
NP pbds_ { using NP __gnu_pbds;
TP<CL T,CL V=null_type,CL C=less<>>using order_tree=tree<T,V,C,rb_tree_tag,tree_order_statistics_node_update>;
}
using pbds_::order_tree;
inline NP type_traits {
ST __empty {};
TP<CL,CL...>auto _req_impl(...)->false_type;
TP<CL R,CL... A,CL=decltype(&R::TP freq<A...>)>auto _req_impl(int)->true_type;
TP<CL R,CL... A>IC BL requires_=decltype(_req_impl<R,A...>(0))::value;
TP<BL E,CL T=int>using requires_expr=enable_if_t<E,T>;
TP<size_t I>ST tag:tag<I-1>{};TP<>ST tag<0>{};
TP<BL B,CL...>IC BL boolT=B; 
TP<BL B,auto...>IC BL boolV=B;
//[remove.cvref]
TP<CL T>ST type_identity{using type=T;};
TP<CL T>using type_identity_t=TY type_identity<T>::type;
TP<CL T>ST remove_cvref : remove_cv<remove_reference_t<T>>{};
TP<CL T>using remove_cvref_t=TY remove_cvref<T>::type;
//[common.reference]
TP<TPP AliasT,CL... A>auto exists_helper(long)->false_type;
TP<TPP AliasT,CL... A,CL=AliasT<A...>>auto exists_helper(int)->true_type;
TP<TPP AliasT,CL... A>
IC BL exists_v=decltype(exists_helper<AliasT,A...>(0))::value;
NP common_detail { 
TP<CL...>ST common_type;
TP<CL T,CL U>ST copy_cv:type_identity<U>{};
TP<CL T,CL U>ST copy_cv<const T,U>:type_identity<add_const_t<U>>{};
TP<CL T,CL U>ST copy_cv<volatile T,U>:type_identity<add_volatile_t<U>>{};
TP<CL T,CL U>ST copy_cv<const volatile T,U>:type_identity_t<add_cv_t<U>>{};
TP<CL T,CL U>using copy_cv_t=TY copy_cv<T,U>::type;
TP<CL T>using cref_t=add_lvalue_reference_t<const remove_reference_t<T>>;
TP<CL T,CL U>using cond_res_t=decltype(1? DCLV(T(&)())() : DCLV(U(&)())());
//For some value of "simple"
TP<CL A,CL B,CL=remove_reference_t<A>,CL=remove_reference_t<B>,CL=void>ST common_ref {};
TP<CL A,CL B>using common_ref_t=TY common_ref<A,B>::type;
TP<CL A,CL B,CL=remove_reference_t<A>,CL=remove_reference_t<B>,CL=void>ST lval_common_ref {};
TP<CL A,CL B,CL X,CL Y>
ST lval_common_ref<A,B,X,Y,enable_if_t<is_reference_v<cond_res_t<copy_cv_t<X,Y>&,copy_cv_t<Y,X>&>>>>
{ using type=cond_res_t<copy_cv_t<X,Y>&,copy_cv_t<Y,X>&>; };
TP<CL A,CL B>using lval_common_ref_t=TY lval_common_ref<A,B>::type;
TP<CL A,CL B,CL X,CL Y>ST common_ref<A&,B&,X,Y>: lval_common_ref<A&,B&>{};
TP<CL X,CL Y>using rref_cr_helper_t=remove_reference_t<lval_common_ref_t<X&,Y&>>&&;
TP<CL A,CL B,CL X,CL Y>ST common_ref<A&&,B&&,X,Y,enable_if_t<
is_convertible_v<A&&,rref_cr_helper_t<X,Y>>&&is_convertible_v<B&&,rref_cr_helper_t<X,Y>>>>
{ using type=rref_cr_helper_t<X,Y>; };
TP<CL A,CL B,CL X,CL Y>ST common_ref<A&&,B&,X,Y,enable_if_t<
is_convertible_v<A&&,lval_common_ref_t<const X&,Y&>>>>
{ using type=lval_common_ref_t<const X&,Y&>; };
TP<CL A,CL B,CL X,CL Y>ST common_ref<A&,B&&,X,Y>: common_ref<B&&,A&>{};
TP<CL>ST xref { TP<CL U>using type=U; };
TP<CL A>ST xref<A&>{ TP<CL U>using type=add_lvalue_reference_t<TY xref<A>::TP type<U>>; };
TP<CL A>ST xref<A&&>{ TP<CL U>using type=add_rvalue_reference_t<TY xref<A>::TP type<U>>; };
TP<CL A>ST xref<const A>{ TP<CL U>using type=add_const_t<TY xref<A>::TP type<U>>; };
TP<CL A>ST xref<volatile A>{ TP<CL U>using type=add_volatile_t<TY xref<A>::TP type<U>>; };
TP<CL A>ST xref<const volatile A>{ TP<CL U>using type=add_cv_t<TY xref<A>::TP type<U>>; };
TP<CL T,CL U,TP<CL>CL TQual,TP<CL>CL UQual>ST basic_common_reference {};
TP<CL...>ST common_reference;
TP<CL... Ts>using common_reference_t=TY common_reference<Ts...>::type;
TP<>ST common_reference<>{};
TP<CL T0>ST common_reference<T0>{ using type=T0; };
TP<CL T,CL U>IC BL has_common_ref_v=exists_v<common_ref_t,T,U>;
TP<CL T,CL U>using basic_common_ref_t=TY basic_common_reference<remove_cvref_t<T>,remove_cvref_t<U>,
xref<T>::TP type,xref<U>::TP type>::type;
TP<CL T,CL U>IC BL has_basic_common_ref_v=exists_v<basic_common_ref_t,T,U>;
TP<CL T,CL U>IC BL has_cond_res_v=exists_v<cond_res_t,T,U>;
TP<CL T,CL U,CL=void>ST binary_common_ref : common_type<T,U>{};
TP<CL T,CL U>ST binary_common_ref<T,U,enable_if_t<has_common_ref_v<T,U>>>: common_ref<T,U>{};
TP<CL T,CL U>ST binary_common_ref<T,U,enable_if_t<has_basic_common_ref_v<T,U>&&!has_common_ref_v<T,U>>>
{ using type=basic_common_ref_t<T,U>; };
TP<CL T,CL U>
ST binary_common_ref<T,U,enable_if_t<has_cond_res_v<T,U>&&!has_basic_common_ref_v<T,U>&&!has_common_ref_v<T,U>>>
{ using type=cond_res_t<T,U>; };
TP<CL T1,CL T2>ST common_reference<T1,T2>: binary_common_ref<T1,T2>{ };
TP<CL Void,CL T1,CL T2,CL...Re>ST multiple_common_reference {};
TP<CL T1,TY T2,CL...Re>ST multiple_common_reference
<void_t<common_reference_t<T1,T2>>,T1,T2,Re...>: common_reference<common_reference_t<T1,T2>,Re...>{};
TP<CL T1,CL T2,CL... R>ST common_reference<T1,T2,R...>: multiple_common_reference<void,T1,T2,R...>{};
//[common.type]
TP<CL...>ST common_type;
TP<CL... Ts>using common_type_t=TY common_type<Ts...>::type;
TP<CL T,CL U>
CEXP BL same_decayed_v=is_same<T,decay_t<T>>::value &&is_same<U,decay_t<U>>::value;
TP<CL T,CL U>using ternary_return_t=decay_t<DCLT(0?DCLV(T):DCLV(U))>;
TP<CL,CL,CL=void>ST binary_common_type{};
TP<CL T,CL U>ST binary_common_type<T,U,enable_if_t<!same_decayed_v<T,U>>>:common_type<decay_t<T>,decay_t<U>>{};
TP<CL T,CL U>ST binary_common_type<T,U,enable_if_t<same_decayed_v<T,U>&&exists_v<ternary_return_t,T,U>>>
{ using type=ternary_return_t<T,U>; };
TP<CL T,CL U>
ST binary_common_type<T,U,enable_if_t<
same_decayed_v<T,U>&&!exists_v<ternary_return_t,T,U>&&exists_v<cond_res_t,cref_t<T>,cref_t<U>>>>
{ using type=decay_t<cond_res_t<cref_t<T>,cref_t<U>>>; };
TP<>ST common_type<>{};
TP<CL T>ST common_type<T>: common_type<T,T>{};
TP<CL T,CL U>ST common_type<T,U>: binary_common_type<T,U>{};
TP<CL Void,CL...>ST multiple_common_type {};
TP<CL T1,CL T2,CL... R>ST multiple_common_type<void_t<common_type_t<T1,T2>>,T1,T2,R...>
: common_type<common_type_t<T1,T2>,R...>{};
TP<CL T1,CL T2,CL... R>ST common_type<T1,T2,R...>: multiple_common_type<void,T1,T2,R...>{};
}//common_detail
using common_detail::common_reference;
using common_detail::common_reference_t;
}
//[concept.same]
TP<CL T,CL U>concept same_as=is_same_v<T,U>;
//[concept.derived]
CpDef(derived_from,CL D,CL B)()(Reqs(is_convertible_v<const volatile D*,const volatile B*>));
TP<CL D,CL B>concept derived_from=is_base_of_v<B,D>&&CpRef(derived_from,D,B);
//[concept.convertible]
CpDef(convertible_to,CL From,CL To)(add_rvalue_reference_t<From>(&f)())(
static_cast<To>(f()),
);
TP<CL From,CL To>concept convertible_to=is_convertible_v<From,To>&&CpRef(convertible_to,From,To);
//[concept.commonref]
CpDef(common_reference_with,CL T,CL U)()(
Reqs(same_as<common_reference_t<T,U>,common_reference_t<U,T>>)
Reqs(convertible_to<T,common_reference_t<T,U>>)
Reqs(convertible_to<U,common_reference_t<T,U>>)
);
TP<CL T,CL U>concept common_reference_with=CpRef(common_reference_with,T,U);
//[concepts.common]
CpDef(common_with,CL T,CL U)()(
Reqs(same_as<common_type_t<T,U>,common_type_t<U,T>>)
static_cast<common_type_t<T,U>>(DCLV(T)),
static_cast<common_type_t<T,U>>(DCLV(U)),
Reqs(common_reference_with<add_lvalue_reference_t<const T>,add_lvalue_reference_t<const U>>)
Reqs(common_reference_with<add_lvalue_reference_t<common_type_t<T,U>>,
common_reference_t<add_lvalue_reference_t<const T>,add_lvalue_reference_t<const U>>>)
);
TP<CL T,CL U>concept common_with=CpRef(common_with,T,U);
//[concept.arithmetic]
TP<CL T>concept integral=is_integral_v<T>;
TP<CL T>concept signed_integral=integral<T>&&is_signed_v<T>;
TP<CL T>concept unsigned_integral=integral<T>&&!signed_integral<T>;
TP<CL T>concept floating_point=is_floating_point_v<T>;
//[concept.assignable]
CpDef(assignable_from,CL L,CL R)(L l,R&&r)(
RetReq(same_as,L)(l=FWD(r))
Reqs(common_reference_with<const remove_reference_t<L>&,const remove_reference_t<R>&>)
);
TP<CL L,CL R>concept assignable_from=is_lvalue_reference_v<L>&&CpRef(assignable_from,L,R);
//[concept.destructible]
TP<CL T>concept destructible=is_nothrow_destructible_v<T>;
//[concept.constructible]
TP<CL T,CL... A>concept constructible_from=destructible<T>&&is_constructible_v<T,A...>;
//[concept.default.init]
CpDef(default_initializable,CL T)() (
T{},
::new (static_cast<void*>(nullptr)) T,
);
TP<CL T>concept default_initializable=constructible_from<T>&&CpRef(default_initializable,T);
//[concept.moveconstructible]
TP<CL T>concept move_constructible=constructible_from<T,T>&&convertible_to<T,T>;
//[concept.copyconstructible]
CpDef(copy_constructible,CL T)()(
Reqs(move_constructible<T>&&constructible_from<T,T&>&&convertible_to<T&,T>&&constructible_from<T,const T&>)
Reqs(convertible_to<const T&,T>&&constructible_from<T,const T>&&convertible_to<const T,T>)
);
TP<CL T>concept copy_constructible=CpRef(copy_constructible,T);
//[range.swap]
ST swap_fn{
TP<CL T>static void swap(T&,T&)=delete;TP<CL T,size_t N>static void swap(T(&)[N],T(&)[N])=delete;
TP<CL T,CL U>CEXP static auto impl(T&&t,U&&u,tag<2>)NOEXP_DCLT_RET((void)swap(FWD(t),FWD(u)))
TP<CL T,CL U,size_t N,CL F=swap_fn>CEXP static auto impl(T(&t)[N],U(&u)[N],tag<1>)
NOEXP_DCLT(DCLV(F&)(*t,*u)){for(size_t i=0;i<N;++i)impl(t[i],u[i],tag<2>{});}
TP<CL T>CEXP static auto impl(T& a,T& b,tag<0>)noexcept(is_nothrow_move_constructible_v<T>&&is_nothrow_assignable_v<T&,T>)
->Req(move_constructible<T>&&assignable_from<T&,T>,void) {T temp=move(a);a=move(b);b=move(temp);}
TP<CL T,CL U>auto COP()(T&&t,U&&u)const NOEXP_DCLT_RET(swap_fn::impl(FWD(t),FWD(u),tag<2>{}))
};
NP ranges{inline NP cpo{CPO swap=swap_fn{};}}
//[concept.swappable]
CpDef(swappable,CL T)(T& a,T& b)(Rg swap(a,b),);
TP<CL T>concept swappable=CpRef(swappable,T);
CpDef(swappable_with,CL T,CL U)(T&&t,U&&u) (
Reqs(common_reference_with<T,U>)
Rg swap(FWD(t),FWD(t)),
Rg swap(FWD(u),FWD(u)),
Rg swap(FWD(t),FWD(u)),
Rg swap(FWD(u),FWD(t)),
);
//[concept.boolean_testable]
TP<CL T>concept bool_ts_impl=convertible_to<T,bool>;
CpDef(bool_ts,CL T) (T&&t)(Cret(bool_ts_impl,!FWD(t))());
TP<CL T>concept boolean_testable=bool_ts_impl<T>&&CpRef(bool_ts,T);
#define BLT(...) Cret(boolean_testable,__VA_ARGS__)()
//[concept.equalitycomparable]
CpDef(weakly_equality_comparable_with,CL T,CL U)(const remove_reference_t<T>&t,const remove_reference_t<U>&u)
(BLT(t==u)BLT(t!=u)BLT(u==t)BLT(u!=t));
TP<CL T,CL U>concept weakly_equality_comparable_with=CpRef(weakly_equality_comparable_with,T,U);
TP<CL T>concept equality_comparable=weakly_equality_comparable_with<T,T>;
ST equality_comparable_with_concept {
TP<CL,CL>static auto test(long)->false_type;
TP<CL T,CL U>static auto test(int)->enable_if_t< equality_comparable<T>&&equality_comparable<U>&&
common_reference_with<const remove_reference_t<T>&,const remove_reference_t<U>&>&&
equality_comparable<common_reference_t<const remove_reference_t<T>&,const remove_reference_t<U>&>>&&
weakly_equality_comparable_with<T,U>,true_type>;
};
TP<CL T,CL U>concept equality_comparable_with=decltype(equality_comparable_with_concept::test<T,U>(0))::value;
//[concepts.totallyordered] 
CpDef(partially_ordered_with,CL T,CL U)(const remove_reference_t<T>& t,const remove_reference_t<U>& u)
(BLT(t>u)BLT(t<u)BLT(t<=u)BLT(t>=u)BLT(u<t)BLT(u>t)BLT(u<=t)BLT(u>=t));
TP<CL T,CL U>concept partially_ordered_with=CpRef(partially_ordered_with,T,U);
TP<CL T>concept tot_ord=equality_comparable<T>&&partially_ordered_with<T,T>;
CpDef(tot_ord_with,CL T,CL U)()(
Reqs(tot_ord<T>&&tot_ord<U>&&equality_comparable_with<T,U>&&partially_ordered_with<T,U>)
Reqs(tot_ord<common_reference_t<const remove_reference_t<T>&,const remove_reference_t<U>&>>)
);
TP<CL T,CL U>concept tot_ord_with=CpRef(tot_ord_with,T,U);
NP invoke_ {//[todo: simplify]
TP<CL>CEXP BL is_reference_wrapper_v=0;
TP<CL T>CEXP BL is_reference_wrapper_v<reference_wrapper<T>> =1;
ST fn { private:
TP<CL Base,CL T,CL Derived,CL... A>static CEXP auto
impl(T Base::*pmf,Derived&&ref,A&&... a) 
noexcept(noexcept((FWD(ref).*pmf)(FWD(a)...)))
->enable_if_t<is_function<T>::value &&is_base_of<Base,decay_t<Derived>>::value,
decltype((FWD(ref).*pmf)(FWD(a)...))>
{ return (FWD(ref).*pmf)(FWD(a)...); } 
TP<CL Base,CL T,CL RefWrap,CL... A>static CEXP auto
impl(T Base::*pmf,RefWrap&&ref,A&&... a) 
noexcept(noexcept((ref.get().*pmf)(FWD(a)...)))
->enable_if_t<is_function<T>::value &&is_reference_wrapper_v<decay_t<RefWrap>>,
decltype((ref.get().*pmf)(FWD(a)...))>
{ return (ref.get().*pmf)(FWD(a)...); }
TP<CL Base,CL T,CL Pointer,CL... A>static CEXP auto
impl(T Base::*pmf,Pointer&&ptr,A&&... a) 
noexcept(noexcept(((*FWD(ptr)).*pmf)(FWD(a)...)))
->enable_if_t<is_function<T>::value &&!is_reference_wrapper_v<decay_t<Pointer>>&&
!is_base_of<Base,decay_t<Pointer>>::value,
decltype(((*FWD(ptr)).*pmf)(FWD(a)...))>
{ return ((*FWD(ptr)).*pmf)(FWD(a)...); }
TP<CL Base,CL T,CL Derived>static CEXP auto
impl(T Base::*pmd,Derived&&ref) noexcept(noexcept(FWD(ref).*pmd))
->enable_if_t<!is_function<T>::value &&is_base_of<Base,decay_t<Derived>>::value,
decltype(FWD(ref).*pmd)>{ return FWD(ref).*pmd; }
TP<CL Base,CL T,CL RefWrap>
static CEXP auto impl(T Base::*pmd,RefWrap&&ref) noexcept(noexcept(ref.get().*pmd))
->enable_if_t<!is_function<T>::value &&is_reference_wrapper_v<decay_t<RefWrap>>,
decltype(ref.get().*pmd)>{ return ref.get().*pmd; }
TP<CL Base,CL T,CL Pointer>static CEXP auto
impl(T Base::*pmd,Pointer&&ptr) noexcept(noexcept((*FWD(ptr)).*pmd))
->enable_if_t< !is_function<T>::value &&!is_reference_wrapper_v<decay_t<Pointer>>&&
!is_base_of<Base,decay_t<Pointer>>::value,
decltype((*FWD(ptr)).*pmd)>{ return (*FWD(ptr)).*pmd; }
TP<CL F,CL... A>
static CEXP auto impl(F&&f,A&&... a) noexcept(
noexcept(FWD(f)(FWD(a)...)))
->enable_if_t< !is_member_pointer<decay_t<F>>::value,decltype(forward<F>(f)(FWD(a)...))>
{ return FWD(f)(FWD(a)...); }
public:
TP<CL F,CL... A>auto COP ()(F&&f,A&&... a) const noexcept(
noexcept(fn::impl(FWD(f),FWD(a)...)))
->decltype(fn::impl(FWD(f),FWD(a)...))
{ return fn::impl(FWD(f),FWD(a)...); }
};
}//invoke_
IC invoke_::fn my_invoke;
TP<CL Void,CL,CL...>ST invoke_result_helper {};
TP<CL F,CL... A>
ST invoke_result_helper<void_t<decltype(my_invoke(DCLV(F),DCLV(A)...))>,F,A...>{
using type=decltype(my_invoke(DCLV(F),DCLV(A)...));
};
TP<CL F,CL... A>ST invoke_result : invoke_result_helper<void,F,A...>{};
TP<CL F,CL... A>using invoke_result_t=TY invoke_result<F,A...>::type;

//[concept.movable]
CpDef(movable,CL T)()(
Reqs(is_object_v<T>&&move_constructible<T>&&assignable_from<T&,T>&&swappable<T>)
);
TP<CL T>concept movable=CpRef(movable,T);
//[concept.copyable]
CpDef(copyable,CL T)()(
Reqs(copy_constructible<T>&&movable<T>)
Reqs(assignable_from<T&,T&>&&assignable_from<T&,const T&>&&assignable_from<T&,const T>)
);
TP<CL T>concept copyable=CpRef(copyable,T);
//[concept.semiregular]
TP<CL T>concept semiregular=copyable<T>&&default_initializable<T>;
//[concept.regular]
TP<CL T>concept regular=semiregular<T>&&equality_comparable<T>;
//[concept.invocable]
ST invocable_concept {
#if (defined(__clang_major__) &&(defined(__apple_build_version__) ||__clang_major__<7))
TP<CL F,CL... A>auto freq(F&&f,A&&... a)->invoke_result_t<F,A...>;
#else
TP<CL F,CL... A>auto freq(F&&f,A&&... a)->decltype( my_invoke(FWD(f),FWD(a)...) );
#endif
};
TP<CL F,CL... A>concept invocable=CpRef(invocable,F,A...);
//[concept.regularinvocable]
TP<CL F,CL... A>concept regular_invocable=invocable<F,A...>;
//[concept.predicate]
CpBl(predicate,CL F,CL...A)(regular_invocable<F,A...>&&boolean_testable<invoke_result_t<F,A...>>);
TP<CL F,CL... A>concept predicate=CpRef(predicate,F,A...);
//[concept.relation]
TP<CL R,CL T,CL U>concept relation=predicate<R,T,T>&&predicate<R,U,U>&&predicate<R,T,U>&&predicate<R,U,T>;
//[concept.equiv]
TP<CL R,CL T,CL U>concept equivalence_relation=relation<R,T,U>;
//[concept.strictweakorder]
TP<CL R,CL T,CL U>concept strict_weak_order=relation<R,T,U>;


CpDef(tplk, CL T)()(RetReq(same_as,size_t)(tuple_size_v<T>));//[todo]more
TP<CL T>concept tuple_like=CpRef(tplk,T);

inline NP utility {

TP<CL T>decay_t<T>CEXP decay_copy(T&&t) { return FWD(t); }
IC ST auto_fn { 
TP<CL T>decay_t<T>COP ()(T&&t) const { return FWD(t); }
TP<CL T>decay_t<T>FCOP %(T&&t,auto_fn) { return FWD(t); }
} Auto;
//[utility.move]
IC ST move_fn { 
TP<CL T>DCLT(auto) COP ()(T&&t) const { return move(t); }
TP<CL T>DCLT(auto) FCOP %(T&&t,move_fn) { return move(t); }
} Move;
//[utility.Ycomb]
TP<CL Fun>ST Y_combinator { Fun fun_;
TP<CL F>Y_combinator(F&&fun): fun_(FWD(fun)) {} 
TP<CL... A>DCLT(auto) COP ()(A&&...a) const { return fun_(*this,(A&&)a...); }
};
TP<CL T>Y_combinator(T)->Y_combinator<T>;
//[utility.scope_guard]
TP<CL F>ST scope_guard { F f; TP<CL FF>scope_guard(FF&&f) : f(FWD(f)) {} ~scope_guard() { f(); } };
TP<CL F>scope_guard(F)->scope_guard<F>;
}//utility
inline NP integer {
TP<CL T>CEXP make_unsigned_t<T>to_unsigned(T t) noexcept { return t; }
TP<CL T>CEXP make_signed_t<T>to_signed(T t) noexcept { return t; }
TP<CL T>CEXP T __rotl(T x,int s) noexcept {
CEXP auto _Nd=numeric_limits<T>::digits;
const int r=s % _Nd;
if (r==0) return x;
else if (r>0) return (x << r) | (x >>((_Nd-r) % _Nd));
else return (x >>-r) | (x << ((_Nd + r) % _Nd));//rotr(x,-r)
}
TP<CL T>CEXP T __rotr(T x,int s) noexcept {
CEXP auto _Nd=numeric_limits<T>::digits;
const int r=s % _Nd;
if (r==0) return x;
else if (r>0) return (x >>r) | (x << ((_Nd-r) % _Nd));
else return (x <<-r) | (x >>((_Nd + r) % _Nd));//rotl(x,-r)
}
TP<CL T>CEXP int __countl_zero(T x) noexcept {
CEXP auto _Nd=numeric_limits<T>::digits;
if (x==0) return _Nd;
CEXP auto _Nd_ull=numeric_limits<ull>::digits;
CEXP auto _Nd_ul=numeric_limits<unsigned long>::digits;
CEXP auto _Nd_u=numeric_limits<unsigned>::digits;
if CEXP(_Nd<=_Nd_u) {
CEXP int diff=_Nd_u-_Nd;
return __builtin_clz(x)-diff;
} else if CEXP(_Nd<=_Nd_ul) {
CEXP int diff=_Nd_ul-_Nd;
return __builtin_clzl(x)-diff;
} else if CEXP(_Nd<=_Nd_ull) {
CEXP int diff=_Nd_ull-_Nd;
return __builtin_clzll(x)-diff;
} else { 
ull high=x >>_Nd_ull;
if (high!=0) {
CEXP int diff=(2*_Nd_ull)-_Nd;
return __builtin_clzll(high)-diff;
}
CEXP auto __max_ull=numeric_limits<ull>::max();
ull __low=x & __max_ull;
return (_Nd-_Nd_ull) + __builtin_clzll(__low);
}
}
TP<CL T>CEXP int __countl_one(T x) noexcept {
if (x==numeric_limits<T>::max()) return numeric_limits<T>::digits;
return __countl_zero<T>((T)~x);
}
TP<CL T>CEXP int __countr_zero(T x) noexcept {
CEXP auto _Nd=numeric_limits<T>::digits;
if (x==0) return _Nd;
CEXP auto _Nd_ull=numeric_limits<ull>::digits;
CEXP auto _Nd_ul=numeric_limits<unsigned long>::digits;
CEXP auto _Nd_u=numeric_limits<unsigned>::digits;
if CEXP(_Nd<=_Nd_u) return __builtin_ctz(x);
else if CEXP(_Nd<=_Nd_ul) return __builtin_ctzl(x);
else if CEXP(_Nd<=_Nd_ull) return __builtin_ctzll(x);
else {
CEXP auto __max_ull=numeric_limits<ull>::max();
ull __low=x & __max_ull;
if (__low!=0) return __builtin_ctzll(__low);
ull high=x >>_Nd_ull;
return __builtin_ctzll(high) + _Nd_ull;
}
}
TP<CL T>CEXP int __countr_one(T x) noexcept {
if (x==numeric_limits<T>::max()) return numeric_limits<T>::digits;
return __countr_zero((T)~x);
}
TP<CL T>CEXP int __popcount(T x) noexcept {
CEXP auto _Nd=numeric_limits<T>::digits;
if (x==0) return 0;
CEXP auto _Nd_ull=numeric_limits<ull>::digits;
CEXP auto _Nd_ul=numeric_limits<unsigned long>::digits;
CEXP auto _Nd_u=numeric_limits<unsigned>::digits;
if CEXP(_Nd<=_Nd_u) return __builtin_popcount(x);
else if CEXP(_Nd<=_Nd_ul) return __builtin_popcountl(x);
else if CEXP(_Nd<=_Nd_ull) return __builtin_popcountll(x);
else {//(_Nd>_Nd_ull)
static_assert(_Nd<=(2*_Nd_ull),"Maximum supported integer size is 128-bit");
CEXP auto __max_ull=numeric_limits<ull>::max();
ull __low=x & __max_ull;
ull high=x >>_Nd_ull;
return __builtin_popcountll(__low) + __builtin_popcountll(high);
}
}
TP<CL T>CEXP BL __has_single_bit(T x) noexcept { return __popcount(x)==1; }
TP<CL T>CEXP T __bit_ceil(T x) noexcept {
CEXP auto _Nd=numeric_limits<T>::digits;
if (x==0 || x==1) return 1;
auto shift_exponent=_Nd-__countl_zero((T)(x-1u));
using __promoted_type=decltype(x << 1);
if CEXP(!is_same<__promoted_type,T>::value) {
const int __extra_exp=sizeof(__promoted_type) / sizeof(T) / 2;
shift_exponent |= (shift_exponent & _Nd) << __extra_exp;
}
return (T)1u << shift_exponent;
}
TP<CL T>CEXP T __bit_floor(T x) noexcept {
CEXP auto _Nd=numeric_limits<T>::digits;
if (x==0) return 0;
return (T)1u << (_Nd-__countl_zero((T)(x >>1)));
}
TP<CL T>CEXP T __bit_width(T x) noexcept {
CEXP auto _Nd=numeric_limits<T>::digits;
return _Nd-__countl_zero(x);
}
TP<CL T,CL U=T>using breq=enable_if_t<is_integral_v<T>,U>;//&&is_unsigned_v<T>,U>;
//[bit.cast]
TP<CL To,CL From,enable_if_t<sizeof(To)==sizeof(From),int> =0>
auto bit_cast(const From &src) noexcept { To dst; memcpy(&dst,&src,sizeof(To)); return dst; }
//[bit.rot],rotating
///Rotate `x` to the left by `s` bits.
IC ST { TP<CL T>breq<T>COP ()(T x,int s) const noexcept RET(__rotl(x,s)) } rotl;
///Rotate `x` to the right by `s` bits.
IC ST { TP<CL T>breq<T>COP ()(T x,int s) const noexcept RET(__rotr(x,s)) } rotr;
#define TMP(RET,NAME) IC ST { TP<CL T>breq<T,RET>COP ()(T x) const noexcept { return __##NAME(x); } } NAME;
//[bit.count],counting
TMP(int,countl_zero)  ///The number of contiguous zero bits,starting from the highest bit.
TMP(int,countl_one )  ///The number of contiguous one bits,starting from the highest bit.
TMP(int,countr_zero)  ///The number of contiguous zero bits,starting from the lowest bit.
TMP(int,countr_one )  ///The number of contiguous one bits,starting from the lowest bit.
TMP(int,popcount   )  ///The number of bits set in `x`.
//[bit.pow.two],integral powers of 2
TMP(bool,has_single_bit)  ///True if `x` is a power of two,0 otherwise.
TMP(T,bit_ceil)///The smallest power-of-two not less than `x`.
TMP(T,bit_floor)  ///The largest power-of-two not greater than `x`.
TMP(T,bit_width)  ///The smallest integer greater than the base-2 logarithm of `x`.
#undef TMP
}
NP ranges{
CPO invoke=my_invoke;
using std::empty,std::data;
inline NP unsp {
auto size=[](auto&&x) DCLT_RET(std::size(FWD(x)));
auto begin=[](auto&&x) DCLT_RET(std::begin(FWD(x)));
auto end=[](auto&&x) DCLT_RET(std::end(FWD(x)));
auto iter_swap=[](auto&&x,auto&&y)DCLT_RET(std::iter_swap(FWD(x),FWD(y)));
auto iter_move=[](auto&&i)DCLT_RET(move(*FWD(i)));
}
}
inline NP algo {
ST identity{TP<CL T>DCLT(auto)COP()(T&&t)const RET((T&&)t)};
TP<CL C=less<>,CL P=identity>ST proj_cmp{
C c;P p;
TP<CL X,CL Y>proj_cmp(X&&x,Y&&y):c((X&&)x),p((Y&&)y) {}
TP<CL T,CL U>BL COP()(T&&t,U&&u)const RET(Rg invoke(c,Rg invoke(p,(T&&)t),Rg invoke(p,(U&&)u)))
};
TP<CL C,CL P>proj_cmp(C,P)->proj_cmp<C,P>;
}
inline NP ITER {
//[iterator.primitives]
//[std.iterator.tags]
using ip_i_tag=input_iterator_tag;
using fw_i_tag=forward_iterator_tag;
using bd_i_tag=bidirectional_iterator_tag;
using ra_i_tag=random_access_iterator_tag;
ST ct_i_tag : ra_i_tag {};
//[incrementable.traits]
TP<CL T>ST incrementable_traits;
TP<CL,CL=Req(1)>ST inti{};
TP<CL T>ST cond_d{using difference_type=T;};
TP<>ST inti<void*>{};
TP<CL T>ST inti<T*>:cond_d<ptrdiff_t>{};
TP<CL I>ST inti<const I>:incrementable_traits<I>{};
CpDef(has_diff,CL T)(TY T::difference_type)();
TP<CL T>ST inti<T,Req(CpRef(has_diff,T))>: cond_d<TY T::difference_type>{};
CpDef(can_diff,CL T)(const T&a,const T&b)(RetReq0(integral)(a-b));
TP<CL T>ST inti<T,Req(!is_pointer_v<T>&&!CpRef(has_diff,T) &&CpRef(can_diff,T))>
: cond_d<make_signed_t<decltype(DCLV(T)-DCLV(T))>>{};
TP<CL T>ST incrementable_traits : inti<T>{};
#define rdtr ind_rd_traits
TP<CL T,CL=int>ST cond_v{};TP<CL T>ST cond_v<T,Req(is_object_v<T>)>{using value_type=remove_cv_t<T>;};
CpDef(m_val,CL T)(TY T::value_type)();
CpDef(m_elem,CL T)(TY T::element_type)();
TP<CL T,CL=int>ST rdtr{};
TP<CL T>ST rdtr<T*>:cond_v<T>{};
TP<CL T>ST rdtr<T,Req(is_array_v<T>)>:cond_v<remove_extent_t<T>>{};
TP<CL T>ST rdtr<const T>:rdtr<T>{};
#define cond(a,b)a CpRef(m_val,T)&&b CpRef(m_elem,T)
#define sacd(a)a same_as<TY T::value_type,TY T::element_type>
TP<CL T>ST rdtr<T,Req(cond(,!))>:cond_v<TY T::value_type>{};
TP<CL T>ST rdtr<T,Req(cond(!,))>:cond_v<TY T::element_type>{};
TP<CL T>ST rdtr<T,Req(cond(,)&&sacd(!))>{};
TP<CL T>ST rdtr<T,Req(cond(,)&&sacd())>:cond_v<TY T::value_type>{};
#undef rdtr
#undef sacd
TP<CL T>using id_t=TY incrementable_traits<T>::difference_type;
TP<CL I>using iv_t=TY ind_rd_traits<I>::value_type;
TP<CL T>using ir_t=decltype(*DCLV(T&));
TP<CL T>using irr_t=decltype(Rg iter_move(DCLV(T&)));
//[iter.concept]
TP<CL,CL=void>IC BL has_iter_tag=0;
TP<CL T>IC BL has_iter_tag<T,void_t<TY iterator_traits<T>::iterator_category>> =1;
TP<CL,CL=void>IC BL has_iter_concept=0;
TP<CL T>IC BL has_iter_concept<T,void_t<TY T::iterator_concept>> =1;
TP<CL T>CEXP auto iter_concept_impl() {
if CEXP(is_pointer_v<T>) return ct_i_tag {};
else if CEXP(has_iter_concept<T>) return TY T::iterator_concept {};
else if CEXP(has_iter_tag<T>) 
return TY iterator_traits<T>::iterator_category {};
}
TP<CL T>using iter_concept=decltype(iter_concept_impl<T>());
CpDef(can_reference,CL I)(I&)();
TP<CL I>concept can_reference=CpRef(can_reference,I);
//[iterator.concept]
CpDef(ind_read,CL I,CL V=iv_t<I>,CL R=ir_t<I>,CL RR=irr_t<I>)(const I i)(
Cret(same_as,*i)(R)Cret(same_as,Rg iter_move(i))(RR)
Creq(common_reference_with<R&&,V&>)Creq(common_reference_with<R&&,RR&&>)Creq(common_reference_with<RR&&,const V&>)
);
TP<CL I>concept ind_rd=CpRef(ind_read,remove_cvref_t<I>);
CpDef(ind_wri,CL O,CL T)(O&&o,T&&t)(*o=FWD(t),*FWD(o)=FWD(t),);
TP<CL I>using ic_t=common_reference_t<ir_t<I>,iv_t<I>&>;
TP<CL O,CL T>concept ind_wr=CpRef(ind_wri,O,T);
//[iterator.concept.winc]
CpDef(winc,CL I)(I i)(
Creq(signed_integral<id_t<I>>)
Cret(same_as,++i)(I&)
i++,
);
TP<CL I>concept winc=movable<I>&&CpRef(winc,I);
ST df_t {}; IC df_t df {};
IC ST unr_t{
#define H TpReq(CL I)(winc<I>)BL FCOP
H==(I,unr_t)RET(0)H!=(I,unr_t)RET(1)H==(unr_t,I)RET(0)H!=(unr_t,I)RET(1)
#undef H
}unr;
CpDef(inc,CL I)(I i)(Cret(same_as,i++)(I));
TP<CL I>concept incrementable=regular<I>&&winc<I>&&CpRef(inc,I);
//[iterator.concept.iterator]
CpDef(io_i,CL I)(I i) (
Creq(can_reference<decltype(*i)>)
);
TP<CL I>concept io_i=winc<I>&&CpRef(io_i,I);
//[iterator.concept.sentinel] [[todo]]
TP<CL S,CL I>concept sentinel_for=semiregular<S>&&io_i<I>&&weakly_equality_comparable_with<S,I>;
//[iterator.concept.sizedsentinel]
CpDef(sized_sentinel_for,CL S,CL I)(const I& i,const S& s)(
Cret(same_as,s-i)(id_t<I>)
Cret(same_as,i-s)(id_t<I>)
);
TP<CL S,CL I>concept sized_sentinel_for=sentinel_for<S,I>&&CpRef(sized_sentinel_for,S,I);
//[iterator.concept.input]
CpBl(ip_i,CL I)(derived_from<iter_concept<I>,ip_i_tag>);
TP<CL I>concept ip_i=io_i<I>&&CpRef(ip_i,I);
CpBl(fw_i,CL I)(derived_from<iter_concept<I>,fw_i_tag>);
TP<CL I>concept fw_i=ip_i<I>&&CpRef(fw_i,I);
CpBl(bd_i,CL I)(derived_from<iter_concept<I>,bd_i_tag>);
TP<CL I>concept bd_i=fw_i<I>&&CpRef(bd_i,I);
CpBl(ra_i,CL I)(derived_from<iter_concept<I>,ra_i_tag>);
TP<CL I>concept ra_i=bd_i<I>&&CpRef(ra_i,I);
CpBl(ct_i,CL I)(derived_from<iter_concept<I>,ct_i_tag>);
TP<CL I>concept ct_i=ra_i<I>&&CpRef(ct_i,I);
CpDef(ind_ui,CL F,CL I,CL V=iv_t<I>&,CL R=ir_t<I>)()(
Creq(invocable<F&,V>&&invocable<F&,R>&&invocable<F&,ic_t<I>>)
Creq(common_reference_with<invoke_result_t<F&,V>,invoke_result_t<F&,R>>)
);
TP<CL F,CL I>concept ind_ui=ind_rd<I>&&copy_constructible<F>&&CpRef(ind_ui,F,I);
CpDef(ind_bp,CL F,CL I,CL J,CL VI=iv_t<I>&,CL VJ=iv_t<J>&,CL RI=ir_t<I>,CL RJ=ir_t<J>)()(
Creq(predicate<F&,VI,VJ>&&predicate<F&,VI,RJ>&&predicate<F&,RI,VJ>&&predicate<F&,RI,RJ>)
Creq(predicate<F&,ic_t<I>,ic_t<J>>)
);
TP<CL F,CL I,CL J=I>concept ind_bp=ind_rd<I>&&ind_rd<J>&&copy_constructible<F>&&CpRef(ind_bp,F,I,J);
TP<CL F,CL...I>using ind_res_t=invoke_result_t<F,ir_t<I>...>;
TP<CL,CL,CL=int>ST projected{};
TP<CL I,CL P>ST projected<I,P,Req(ind_rd<I>&&ind_ui<P,I>)>:cond_v<remove_cvref_t<ind_res_t<P&,I>>>{ind_res_t<P&,I>operator*()const;};
//[alg.req]
CpDef(ind_mov,CL I,CL O)()(Creq(ind_rd<I>)Creq(ind_wr<O,irr_t<I>>));
TP<CL I,CL O>concept indirectly_movable=CpRef(ind_mov,I,O);
TP<CL I,CL J,CL R,CL P=identity,CL Q=identity>
concept ind_cmp=ind_bp<R,projected<I,P>,projected<J,Q>>;
}//ITER
NP ranges {
//[todo]
CpDef(ind_sw,CL I,CL J)(I&i,J&j)(Rg iter_swap(i,j),Rg iter_swap(j,i),Rg iter_swap(i,i),Rg iter_swap(j,j),);
TP<CL I,CL J=I>concept ind_sw=ind_rd<I>&&ind_rd<J>&&CpRef(ind_sw,I,J);
//[range.iter.op]
IC ST advance_fn {
TpReq(CL I)(io_i<I>)void COP()(I& i,id_t<I>n) const
{if CEXP(ra_i<I>)i+=n;else{if(n>=0)while (n--)++i;else if CEXP(bd_i<I>)while(n++)--i;}}
TpReq(CL I,CL S)(sentinel_for<S,I>)void COP()(I& i,S s) const 
{if CEXP(assignable_from<I&,S>) i=move(s);else if CEXP(sized_sentinel_for<S,I>)(*this)(i,s-i);else while(i!=s)++i;}
TpReq(CL I,CL S)(sentinel_for<S,I>)void COP()(I&i,id_t<I> n,S s)const{
    if CEXP(sized_sentinel_for<S,I>){if(abs(n)>=abs(s-i))(*this)(i,s);else(*this)(i,n);}
    else{if(n<0){if CEXP(bd_i<I>)while(n++&&i!=s)--i;}else while(n--&&i!=s)++i;}
}
} advance;
IC ST next_fn {
TpReq(CL I)(io_i<I>) I COP()(I x) const RET(++x)
TP<CL I,CL...A>auto COP()(I x,A... a)const NOEXP_DCLT_RET((advance(x,a...),x)%Auto)
}next;
IC ST prev_fn {
TpReq(CL I)(bd_i<I>)I COP()(I x) const RET(--x)
TpReq(CL I,CL...A)(bd_i<I>)auto COP()(I x,A...a)const NOEXP_DCLT_RET((advance(x,a...),-x)%Auto)
}prev;

//[ranges.range] concepts
CpDef(range,CL T)(T& t)(Rg begin(t),Rg end(t),);
TP<CL T>concept range=CpRef(range,T);
TP<CL>IC BL enable_borrowed_rg=0;
TP<CL T>concept borrowed_rg=range<T>&&(is_lvalue_reference_v<T>|| enable_borrowed_rg<remove_cvref_t<T>>);
TP<CL T>using i_t=decltype(Rg begin(DCLV(T&)));
TP<CL T>using s_t=decltype(Rg end(DCLV(T&)));
TP<CL R>using rs_t=decltype(Rg size(DCLV(R&)));
TP<CL R>using rd_t=id_t<i_t<R>>;
TP<CL R>using rv_t=iv_t<i_t<R>>;
TP<CL R>using rr_t=ir_t<i_t<R>>;
TP<CL R>using rrr_t=irr_t<i_t<R>>;
CpDef(sz_rg,CL T)(T& t)(Rg size(t),);
TP<CL T>concept sz_rg=range<T>&&CpRef(sz_rg,T);
//[range.refinements]
//[todo]output_rg
CpBl(ip_rg,CL T)(ip_i<i_t<T>>);
TP<CL T>concept ip_rg=range<T>&&CpRef(ip_rg,T);
CpBl(fw_rg,CL T)(fw_i<i_t<T>>);
TP<CL T>concept fw_rg=ip_rg<T>&&CpRef(fw_rg,T);
CpBl(bd_rg,CL T)(bd_i<i_t<T>>);
TP<CL T>concept bd_rg=fw_rg<T>&&CpRef(bd_rg,T);
CpBl(ra_rg,CL T)(ra_i<i_t<T>>);
TP<CL T>concept ra_rg=fw_rg<T>&&CpRef(ra_rg,T);
CpDef(ct_rg,CL T)(T& t)(RetReq(same_as,add_pointer_t<rr_t<T>>) (Rg data(t)));
TP<CL T>concept ct_rg=range<T>&&CpRef(ct_rg,T);
CpBl(cm_rg,CL R)(same_as<i_t<R>,s_t<R>>);
TP<CL R>concept cm_rg=range<R>&&CpRef(cm_rg,R);
//[interfaces]
TP<CL D>CL view_interface {
CEXP D& derived() noexcept RET(static_cast<D&>(*this))
CEXP const D& derived() const noexcept RET(static_cast<const D&>(*this))
public: using __interface=view_interface;
LazyT(D,fw_rg<t>) CEXP BL empty() RET(begin(derived())==end(derived()))
LazyT(D,fw_rg<const t>) CEXP BL empty() const RET(begin(derived())==end(derived()))
LazyT(D,ReqExpr(Rg empty(DCLV(t&)))) explicit COP bool() RET(!Rg empty(derived()) )
LazyT(D,ReqExpr(Rg empty(DCLV(t&)))) explicit COP bool() const RET(!Rg empty(derived()) )
LazyT(D,ReqExpr(range<D>&&ct_i<i_t<t>>)) CEXP auto data()
->decltype(&*Rg begin(DCLV(t&)))RET(&*begin(derived()))
LazyT(D,ReqExpr(range<const D>&&ct_i<i_t<const t>>)) CEXP auto data()
const->decltype(&*Rg begin(DCLV(const t&))) RET(&*begin(derived()))
LazyT(D,fw_rg<t>&&sized_sentinel_for<s_t<t>,i_t<t>>)
CEXP auto size() RET(Rg end(derived())-Rg begin(derived()))
LazyT(D,fw_rg<const t>&&sized_sentinel_for<s_t<const t>,i_t<const t>>)
CEXP auto size() const RET(end(derived())-::begin(derived()))
LazyT(D,fw_rg<t>) CEXP DCLT(auto) front() RET(*begin(derived()))
LazyT(D,fw_rg<const t>) CEXP DCLT(auto) front() const RET(*begin(derived()))
LazyT(D,bd_rg<t>&&cm_rg<t>) CEXP DCLT(auto) back() RET(*prev(end(derived())))
LazyT(D,bd_rg<const t>&&cm_rg<const t>) CEXP DCLT(auto) back() const RET(*prev(end(derived())))
LazyT(D,ra_rg<t>) DCLT(auto) COP[](rd_t<t>n) RET(begin(derived())[n])
LazyT(D,ra_rg<t>) DCLT(auto) COP[](rd_t<t>n) const RET(begin(derived())[n])
};
TP<CL I,CL Tg,CL D,CL V, CL Ref>CL IF{//Need: adv inc dec,friend: dif lt eq:lt:df_t
#define TgD(v)static IC BL v=derived_from<Tg,v##_i_tag>;
TgD(fw)TgD(bd)TgD(ra)
#undef TgD
using R=I&;using CR=const I&;
R CEXP It()RET(R(*this)) CR CEXP It()const RET(CR(*this))
#define RT(...) { __VA_ARGS__; return R(*this); }
public:using pointer=void;using iterator_category=Tg;using iterator_concept=Tg;using difference_type=D;using value_type=V;using reference=Ref;
R COP++()RT(It().inc())auto COP++(int){ if CEXP(fw) DefSuffix(++) else ++*this; }
LazyT(I,bd)R COP--()RT(It().dec())LazyT(I,bd)I COP--(int)DefSuffix(--)
LazyT(I,ra)R COP+=(D n)RT(It().adv(n))LazyT(I,ra)R COP-=(D n)RT(It().adv(-n))
LazyT(I,ra)I FCOP+(const IF&i,D n){I j=i.It();R(j)+=n;return j;}LazyT(I,ra)I FCOP+(D n,const IF&i)RET(i+n)
LazyT(I,ra)I FCOP-(const IF&i,D n){I j=i.It();R(j)-=n;return j;}LazyT(I,ra)D FCOP-Crefp(IF)RET(dif(i.It(),j.It()))
LazyT(I,ra)DCLT(auto) COP[](D n)RET(*(*this+n).It())
#define Def(Na,X) ReqExpr(Na(DCLV(X),DCLV(X)))
LazyT(I,Def(eq,t&))BL FCOP==Crefp(IF) RET(eq(i.It(),j.It()))LazyT(I,Def(eq,t&))BL FCOP!=Crefp(IF) RET(!(i==j))
#define Deff LazyT(I,ra&&Def(lt,const t&))
Deff BL FCOP<Crefp(IF) RET(lt(i.It(),j.It()))Deff BL FCOP>Crefp(IF) RET(j<i)
Deff BL FCOP<=Crefp(IF) RET(!(j<i))Deff BL FCOP>=Crefp(IF) RET(!(i<j))
#undef Deff
#define Deff LazyT(I,ReqExpr(DCLV(t&).rte()))
#define AA (const IF&i,df_t)
#define BB (df_t,const IF&i)
#define EE RET(i.It().rte())
#define NN RET(!i.It().rte())
Deff BL FCOP==AA EE Deff BL FCOP==BB EE Deff BL FCOP!=AA NN Deff BL FCOP!=BB NN
#undef AA
#undef BB
#undef NN
#undef EE
#undef Deff
#undef Def
#undef RT
};
TP<CL S>CL SF{
using R=S&;using CR=const S&;
public:
#define P1 (const S&i,const I&j)RET
#define P2 (const I&i,const S&j)RET
#define Def TpReq(CL I,CL t=S)(ReqExpr(DCLV(t&).eq(DCLV(I&))))BL FCOP
Def==P1(CR(i).eq(j)) Def!=P1(!(i==j)) Def==P2(j==i) Def!=P2(!(i==j))
#undef Def
#define Def TpReq(CL I,CL t=S)(ReqExpr(DCLV(t&).eq(DCLV(I&)))) auto FCOP-
Def P1(CR(i).dif(j)) Def P2(-(j-i))
#undef Def
#undef P1
#undef P2
};
//[range.view]
ST view_base{};
CpDef(f_v_i,CL T)()(Reqs(derived_from<T,TY T::__interface>));
TP<CL T>IC BL enable_view=derived_from<T,view_base>|| CpRef(f_v_i,T);
TP<CL T>concept view=range<T>&&movable<T>&&enable_view<T>;
//[range.definements]
TP<CL T>concept viewable_rg=range<T>&&((view<remove_cvref_t<T>>&&constructible_from<remove_cvref_t<T>,T>) ||
!view<remove_cvref_t<T>>&&borrowed_rg<T>);
//[range.utility]
//[range.utility.helper]
TP<CL V>concept simple_view=view<V>&&range<const V>&&
same_as<i_t<V>,i_t<const V>>&&same_as<s_t<V>,s_t<const V>>;
CpDef(has_arrow,CL I)(I i)(
i.operator->(),
);
TP<CL I>concept has_arrow=ip_i<I>&&(is_pointer_v<I>|| CpRef(has_arrow,I));
TP<CL T,CL U>concept different_from=!same_as<remove_cvref_t<T>,remove_cvref_t<U>>;
//[range.dangling]
ST dangling { dangling()noexcept=default;TP<CL...A>dangling(A&&...){} };
TP<CL T>ST box_ : optional<T>{
using optional<T>::optional;
LazyT(T,!default_initializable<T>) box_()=delete;
LazyT(T,default_initializable<T>)CEXP box_()noexcept(is_nothrow_default_constructible_v<T>):optional<T>{in_place}{}
box_(const box_&)=default;box_(box_&&)=default;
box_&operator=(const box_&other)RET_THIS(
    if CEXP(assignable_from<T&,const T&>)this->TP optional<T>::operator=((const optional<T>&)other);
    else if (this!=addressof(other)){if(other)this->emplace(*other);else this->reset();}
)
box_& operator=(box_&&other)RET_THIS(
if CEXP (assignable_from<T&,T>)this->TP optional<T>::operator=((optional<T>&&)(other));
else if (this!=addressof(other)) { if (other) this->emplace(move(*other)); else this->reset();} 
)
};
TP<CL T>using copyable_box=box_<T>;
#define Def_Adap1(Na) NP views{IC ST Na##_fn {TP<CL T>auto COP()(T&&t) const NOEXP_DCLT_RET(Na##_view{FWD(t)})\
TP<CL T>auto FCOP|(T&&t,Na##_fn f) NOEXP_DCLT_RET(f(FWD(t)))} Na;}
//[range.subrange]
enum CL subrange_kind {sized,unsized};
TP<CL From,CL To>concept convertible_to_non_slicing=
convertible_to<From,To>&&!(is_pointer_v<decay_t<From>>&&is_pointer_v<decay_t<To>>&&
different_from<remove_pointer_t<decay_t<From>>,remove_pointer_t<decay_t<To>>>);
TP<CL I,CL S=I,subrange_kind K= sized_sentinel_for<S,I>? subrange_kind::sized : subrange_kind::unsized>
CL subrange:public view_interface<subrange<I,S,K>>{
static_assert(io_i<I>);
static_assert(sentinel_for<S,I>);
static_assert(K==subrange_kind::sized || !sized_sentinel_for<S,I>);
static CEXP BL StoreSize=(K==subrange_kind::sized &&!sized_sentinel_for<S,I>);
using sz_t=make_unsigned_t<id_t<I>>;
public:subrange()=default;
TpReq(CL II)(convertible_to_non_slicing<II,I>&&!StoreSize)CEXP subrange(II i,S s):i(move(i)),s{s}{}
TpReq(CL II)(convertible_to_non_slicing<II,I>&&K==subrange_kind::sized)CEXP subrange(II i,S s,sz_t n):i(move(i)),s{s},sz{n}{}
TpReq(CL R)(borrowed_rg<R>&&convertible_to_non_slicing<i_t<R>,I>&&convertible_to<s_t<R>,S>&&StoreSize)
CEXP subrange(R&&r):subrange(r,Rg size(r)){}
TpReq(CL R)(borrowed_rg<R>&&convertible_to_non_slicing<i_t<R>,I>&&convertible_to<s_t<R>,S>&&!StoreSize)
subrange(R&&r):subrange(Rg begin(r),Rg end(r)) {}
TpReq(CL R)(borrowed_rg<R>&&convertible_to_non_slicing<i_t<R>,I>&&convertible_to<s_t<R>,S>&&K==subrange_kind::sized)
CEXP subrange(R&&r,sz_t n):subrange(Rg begin(r),Rg end(r),n) {}
LazyT(I,copyable<I>)CEXP auto begin()const RET(i)
LazyT(I,!copyable<I>)CEXP auto begin()RET(move(i))
CEXP S end()const RET(s)
CEXP BL empty()const RET(i==s)
LazyV(K,K==subrange_kind::sized)CEXP sz_t size()const{if CEXP(StoreSize)return sz; else return to_unsigned(s-i);}
private: I i; S s; [[__no_unique_address__]] conditional_t<StoreSize,sz_t,dangling>sz;
};

TpReq(CL I,CL S)(sentinel_for<S,I>)subrange(I,S)->subrange<I,S>;
TpReq(CL I,CL S)(sentinel_for<S,I>)subrange(I,S,make_unsigned_t<id_t<I>>)->subrange<I,S,subrange_kind::sized>;
TpReq(CL R)(borrowed_rg<R>)subrange(R&&)->subrange<i_t<R>,s_t<R>,
(sz_rg<R>|| sized_sentinel_for<i_t<R>,s_t<R>>) ? subrange_kind::sized : subrange_kind::unsized>;
TpReq(CL R)(borrowed_rg<R>)subrange(R&&,make_signed_t<rd_t<R>>)
->subrange<i_t<R>,s_t<R>,subrange_kind::sized>;
#define Head CL I,CL S,Rg subrange_kind K
#define Name Rg subrange<I,S,K>
#define Body {if CEXP(N==0)RET(r.begin())else RET(r.end())}
TP<size_t N,Head>CEXP auto get(const Name&r)Body TP<size_t N,Head>CEXP auto get(Name&&r)Body
}//ranges
}//my
TP<Head>ST tuple_size<Name>:integral_constant<size_t,2>{};
TP<Head>ST tuple_element<0,Name>:type_identity<I>{};TP<Head>ST tuple_element<0,const Name>:type_identity<I>{};\
TP<Head>ST tuple_element<1,Name>:type_identity<S>{};TP<Head>ST tuple_element<1,const Name>:type_identity<S>{};\
using my::ranges::get;
#undef Head
#undef Name
#undef Body
inline NP my{
NP ranges{
//[single.view]
TpReq(CL T)(is_object_v<T>&&copy_constructible<T>)ST single_view: view_interface<single_view<T>>{
TpReq(CL U)(same_as<remove_cvref_t<U>,T>)CEXP explicit single_view(U&&u):v_(FWD(u)){}
TpReq(CL...A)(constructible_from<T,A...>)CEXP explicit single_view(in_place_t l,A&&...a):v_{l,FWD(a)...}{}
#define Y(Na,Cv,...) CEXP Cv T*Na()Cv noexcept RET(__VA_ARGS__)
#define X(Na,Cv,...) Y(Na,Cv, data() __VA_ARGS__)
X(begin,)X(begin,const,)X(end,,+1)X(end,const,+1)
#undef X
static CEXP size_t size()noexcept RET(1)
Y(data,,v_.operator->())Y(data,const,v_.operator->())
#undef Y
private:copyable_box<T> v_;
};
TP<CL T>single_view(T)->single_view<T>;
Def_Adap1(single)
//[iota.view]
CpDef(dec,CL I)(I i)(RetReq(same_as,I&)(--i)RetReq(same_as,I)(i--));
TP<CL T>concept decrementable=incrementable<T>&&CpRef(dec,T);
CpDef(adv,CL I)(I i,const I j,const id_t<I>n)(
RetReq(same_as,I&)(i+=n)
RetReq(same_as,I&)(i-=n)
I(j+n),
I(n+j),
I(j-n),
Cret(convertible_to,j-j)(id_t<I>)
);
TP<CL T>concept advanceable=decrementable<T>&&tot_ord<T>&&CpRef(adv,T);
TP<CL W,CL B=unr_t>CL iota_view : public view_interface<iota_view<W,B>>{
using Tg=conditional_t<advanceable<W>,ra_i_tag,conditional_t<decrementable<W>,bd_i_tag,
conditional_t<incrementable<W>,fw_i_tag,ip_i_tag>>>;
using D=id_t<W>;
TP<CL I>using F=IF<I,Tg,D,W,W>;
ST S; ST I:public F<I>{
friend F<I>;friend S;W v;
VC inc(){++v;}LazyT(W,1)VC dec(){--v;}
LazyT(W,1)void adv(D n){if CEXP(is_unsigned_v<W>)n>=D(0)?v+=W(n):v-=W(-n);else v+=n;}
LazyT(W,incrementable<W>)BL FC eq Crefp(I) RET(i.v==j.v)
LazyT(W,1)BL FC lt Crefp(I) RET(i.v<j.v)
LazyT(W,1)BL FC dif Crefp(I) 
{if CEXP(is_integral_v<W>){if CEXP(is_signed_v<W>)RET(D(D(i.v)-D(j.v)))else RET(j.v>i.v?D(-D(j.v-i.v)):D(i.v-j.v))}else RET(i.v-j.v)}
public:I()=default;CEXP explicit I(W v):v(v){}W COP*()const RET(v)
};
ST S:SF<S>{
friend SF<S>;
S()=default;CEXP explicit S(B b):b(b) {}
private:B b;
CEXP BL eq(const I&i)const RET(b==i.v)LazyT(W,sized_sentinel_for<B,W>)CEXP BL dif(const I&i)const RET(b-i.v)
};
W v; B b;
public:
iota_view()=default;
CEXP explicit iota_view(W v) : v(v) {}
CEXP iota_view(type_identity_t<W>v,type_identity_t<B>b) : v(v),b(b) {}
CEXP I begin() const { return I{v}; }
CEXP auto end() const {
if CEXP(is_same_v<W,B>) return I{b};
else if CEXP(is_same_v<B,unr_t>) return unr;
else return S{b};
}
LazyT(W,same_as<W,B>|| (integral<W>&&integral<B>) || sized_sentinel_for<B,W>) CEXP auto size() const {
if CEXP(is_integral_v<W>&&is_integral_v<B>)
return v<0 ? b<0 ? to_unsigned(-v)-to_unsigned(-b) : to_unsigned(b) + to_unsigned(-v) : to_unsigned(b)-to_unsigned(v);
else return to_unsigned(b-v);
}
};
TP<CL W,CL B>iota_view(W,B)->iota_view<W,B>;
NP views {
IC ST iota_fn {
TP<CL T>auto COP ()(T&&e) const DCLT_RET( iota_view {FWD(e)} )
TP<CL T,CL U>auto COP ()(T&&e,U&&f) const DCLT_RET( iota_view {FWD(e),FWD(f)} )
} iota;
}
TP<BL C,CL T>using maybe_const=conditional_t<C,const T,T>;
//[range.ref.view]
TpReq(CL R)(range<R>&&is_object_v<R>)CL ref_view:public view_interface<ref_view<R>>{
ST ref_req_concept{static void FUN(R&); static void FUN(R&&)=delete;TP<CL T>auto freq()->decltype(FUN(DCLV(T)));};
R*r;
public:TpReq(CL T)(different_from<T,ref_view>&&convertible_to<T,R&>&&CpRef(ref_req,T))
CEXP ref_view(T&&t):r(&(R&)(FWD(t))){}
CEXP R& base()const RET(*r)
CEXP auto begin() const RET(Rg begin(*r))
CEXP auto end() const RET(Rg end(*r))
LazyT(R,ReqExpr(Rg empty(*DCLV(t)))) CEXP BL empty() const RET(Rg empty(*r))
LazyT(R,sz_rg<R>)CEXP auto size() const RET(Rg size(*r))
LazyT(R,ct_rg<R>)CEXP auto data() const RET(Rg data(*r))
};
TP<CL R>ref_view(R&)->ref_view<R>;
TP<CL>IC BL init_ls=0;TP<CL T>IC BL init_ls<initializer_list<T>> =1;
TpReq(CL R)(movable<R>&&!init_ls<R>)ST owning_view:view_interface<owning_view<R>>{
owning_view()=default;owning_view(R&&r):r_(move(r)){}
#define Es(Na,F,...) LazyT(R,__VA_ARGS__)CEXP auto Na()F RET(Rg Na(r_))
#define Esy(Na,Cond,F) Es(Na,F,Cond<F R>)
Esy(begin,range,)Esy(begin,range,const)Esy(end,range,)Esy(end,range,const)
Esy(size,sz_rg,)Esy(size,sz_rg,const)Esy(data,ct_rg,)Esy(data,ct_rg,const)
Es(empty,,ReqExpr(Rg empty(DCLV(t&))))Es(empty,const,ReqExpr(Rg empty(DCLV(t&))))
#undef Esy
#undef Es
#define Base(F) CEXP R F base() F RET((R F)r_)
Base(&)Base(const&)Base(&&)Base(const&&)
#undef Base
private:R r_;
};
NP views {
IC ST all_fn {
TpReq(CL R)(view<decay_t<R>>) auto CEXP impl(R&&r,tag<2>) const NOEXP_DCLT_RET(decay_copy(FWD(r)))
TP<CL R>auto CEXP impl(R&&r,tag<1>) const NOEXP_DCLT_RET(ref_view{FWD(r)})
TP<CL R>auto CEXP impl(R&&r,tag<0>) const NOEXP_DCLT_RET(owning_view{FWD(r)})
TP<CL T>auto COP ()(T&&t) const NOEXP_DCLT_RET(impl(FWD(t),tag<2>{}))
TP<CL T>auto FCOP |(T&&t,all_fn f) NOEXP_DCLT_RET(f(FWD(t)))
} all;
TP<CL T>using all_t=DCLT(all(DCLV(T)));
}//views
//[range.copy]
ST copy_fn {
TP<CL I,CL S,CL O,CL P>
static O CEXP impl(I f,S l,O o,P p) { for (;f!=l; ++f,++o)*o=invoke(p,*f); return o; }
TP<CL R,CL O,CL P= identity>
O COP ()(R&&r,O o,P p={}) const { return impl(begin(r),end(r),move(o),ref(p)); }
};
IC copy_fn copy;
ST min_fn {
TP<CL I,CL S,CL C,CL P>static auto CEXP impl(I f,S l,C c,P p) {
auto ret=*f;
while (++f!=l) if (invoke(c,invoke(p,*f),invoke(p,ret))) ret=*f;
return ret;
}
TP<CL T,CL C=less<>,CL P=identity>
auto COP()(initializer_list<T>r,C c={},P p={}) const { return impl(begin(r),end(r),move(c),ref(p)); }
};
IC min_fn min;
auto abs=[](auto x)RET(::abs(x));
IC ST sort_fn{
TP<CL I,CL S,CL C,CL P>
static CEXP I impl(I f,S l,C c,P p){auto r=Rg next(f,l);::sort(f,r,proj_cmp(ref(c),ref(p)));return r;}
TpReq(CL R,CL C=less<>,CL P=identity)(ra_rg<R>)//todo sortable
DCLT(auto) COP()(R&&r,C c={},P p={})const RET(impl(Rg begin(r),Rg end(r),ref(c),ref(p)))
} sort;
IC ST fold_fn {//[[todo]]requires
TP<CL I,CL S,CL T,CL Op,CL P>static CEXP auto impl(I f,S l,T t,Op op,P p) {
using U=remove_cvref_t<invoke_result_t<Op&,T,ind_res_t<P&,I>>>;
if(f==l)RET(U(move(t)))U a=invoke(op,move(t),*f);while(++f!=l)a=invoke(op,move(a),invoke(p,*f));return a;
}
TpReq(CL I,CL S,CL T,CL Op=plus<>,CL P=identity)(ip_i<I>&&sentinel_for<S,I>) 
auto COP()(I f,S l,T t,Op op={},P p={}) const RET(impl(move(f),move(l),move(t),ref(op),ref(p)))
TpReq(CL R,CL T,CL Op=plus<>,CL P=identity)(ip_rg<R>)auto COP()(R&&r,T t,Op op={},P p={})const RET(impl(Rg begin(r),Rg end(r),move(t),ref(op),ref(p)))
TP<CL T,CL Op,CL P>ST fn{T t;Op op;P p;
TpReq(CL I,CL S)(ip_i<I>&&sentinel_for<S,I>)auto COP()(I f,S l)RET(impl(move(f),move(l),move(t),ref(op),ref(p)))//[need?]
TpReq(CL R)(ip_rg<R>)auto COP()(R&&r)RET(impl(begin(r),end(r),move(t),ref(op),ref(p)))
TpReq(CL R)(ip_rg<R>)auto FCOP|(R&&r,fn f)RET(impl(begin(r),end(r),move(f.t),ref(f.op),ref(f.p)))
};
TP<CL T,CL Op=plus<>,CL P=identity>auto COP()(T t,Op op={},P p={})const RET(fn<T,Op,P>{move(t),move(op),move(p)})
} fold;
//[view.transform]
TpReq(CL V,CL F)(ip_rg<V>&&view<V>&&copy_constructible<F> &&is_object_v<F>&&
regular_invocable<F&,rr_t<V>>&&can_reference<invoke_result_t<F&,rr_t<V>>>) 
CL transform_view:public view_interface<transform_view<V,F>>{
TP<BL>ST S;
#define B maybe_const<C,V>
#define D rd_t<B>
TP<BL C>using Tg=conditional_t<ra_rg<B>,ra_i_tag,conditional_t<bd_rg<B>,bd_i_tag,conditional_t<fw_rg<B>,fw_i_tag,ip_i_tag>>>;
TP<BL C>using T=remove_cvref_t<invoke_result_t<F&,rr_t<B>>>;//maybe_const<C,F>&?[[todo]]
TP<BL C>using R=invoke_result_t<F&,rr_t<B>>;
#define Fa IF<I<C>,Tg<C>,D,T<C>,R<C>>
TP<BL C>CL I:public Fa{
friend Fa;TP<BL>friend ST S;TP<BL>friend ST I;
#undef Fa
using P=maybe_const<C,transform_view>;using Ty=i_t<B>;
VC inc(){++i_;}LazyT(B,1)VC dec(){--i_;}LazyT(B,1)VC adv(D n){i_+=n;}
LazyT(B,equality_comparable<Ty>) BL FC eq Crefp(I)RET(i.i_==j.i_)
LazyT(B,1)BL FC lt Crefp(I)RET(i.i_<j.i_)LazyT(B,1)D FC dif Crefp(I) RET(i.i_-j.i_)
Ty i_;P*p_;public:
I()=default;CEXP I(P&p,Ty c):p_(&p),i_(c){}LazyT(V,C&&convertible_to<i_t<V>,Ty>)CEXP I(I<!C>i):i_(move(i.i_)),p_(i.p_){}
CEXP auto base()const&RET(i_)CEXP auto base()&&RET(move(i_))
DCLT(auto) COP*() const RET(Rg invoke(*p_->fun_,*i_))
FC DCLT(auto)iter_move(const I&i)NOEXP(Rg invoke(*p_->fun_,*i_)){if CEXP(is_lvalue_reference_v<decltype(*i)>)RET(move(*i))return*i;}
LazyT(B,ind_sw<i_t<B>>)FC auto iter_swap Crefp(I)NOEXP_RET(Rg iter_swap(i.i_,j.i_))
};
TP<BL C>CL S:public SF<S<C>> {
TP<BL>friend ST S;friend SF<S<C>>;
using Pa=maybe_const<C,transform_view>;using Ty=s_t<B>;Ty s_;
#define Def(Na) TpReq(BL CC)(Na##sentinel_for<Ty,i_t<maybe_const<CC,V>>>)
Def()BL eq(const I<CC>&i)const RET(s_==i.i_)Def(sized_)D dif(const I<CC>&i)const RET(s_-i.i_)
#undef D
#undef B
#undef Def
public:CEXP auto base()RET(s_)
S()=default;CEXP S(Ty s):s_(move(s)){}LazyT(V,C&&convertible_to<s_t<V>,Ty>)CEXP S(S<!C>s):s_(move(s.s_)){}
};
V v_=V();
copyable_box<F>fun_;
public:
CEXP transform_view(V base,F fun) : v_(move(base)),fun_(move(fun)) {}
CEXP V base()const RET(v_)
CEXP I<0>begin() RET( {*this,::begin(v_)} )
LazyT(V,range<const V>&&regular_invocable<const F&,rr_t<const V>>)
CEXP I<1>begin() const RET({*this,::begin(v_)})
CEXP auto end() {if CEXP(cm_rg<V>)RET(I<0>{*this,::end(v_)})else RET(S<0>{::end(v_)})}
LazyT(V,range<const V>&&regular_invocable<const F&,rr_t<const V>>) CEXP auto end() const {
if CEXP(cm_rg<V>) return I<1>{*this,::end(v_)};
else return S<1>{::end(v_)};
}
LazyT(V,sz_rg<V>) CEXP auto size() RET(::size(v_) )
LazyT(V,sz_rg<const V>)CEXP auto size() const RET(::size(v_) )
};
TP<CL R,CL F>transform_view(R&&,F)->transform_view<Vw all_t<R>,F>;
NP views {
IC ST transform_fn {
TP<CL E,CL F>auto COP ()(E&&e,F&&f) const DCLT_RET(transform_view {FWD(e),FWD(f)})
TP<CL F>ST fn {
F f;
TP<CL R>auto COP ()(R&&r) const DCLT_RET( transform_view {FWD(r),move(f)} )
TP<CL R>auto FCOP |(R&&r,fn a) DCLT_RET( a(FWD(r)) )
};
TP<CL F>auto COP ()(F&&f) const { return fn<F>{FWD(f)}; }
} transform;
}
IC ST search_fn {
TP<CL I,CL S,CL J,CL T,CL Pr,CL P,CL Q>subrange<I>static impl(I a,S b,J x,T y,Pr pr,P p,Q q){
for (;;++a) {I i=a;
for(J j=x;;++i,++j){if(j==y)RET({a, i})if(i==b)RET({i,i})if(!invoke(pr,invoke(p,*i),invoke(q,*j)))break;}
}
}
TpReq(CL R,CL S,CL Pr=equal_to<>,CL P=identity,CL Q=identity)(fw_rg<R>&&fw_rg<S>&&ind_cmp<i_t<R>,i_t<S>,Pr,P,Q>)
CEXP auto operator()(R&&r,S&&s,Pr pr={},P p={},Q q={})const RET(impl(ALL(r),ALL(s),ref(pr),ref(p),ref(q)))
}search;
//[range.split.view]
TpReq(CL V,CL P)(fw_rg<V>&&view<V>&&fw_rg<P>&&view<P>&&ind_cmp<i_t<V>,i_t<P>,equal_to<>>)
CL split_view:public view_interface<split_view<V,P>>{
V v_;P p_;
using VI=i_t<V>;using R=subrange<VI>;
R CEXP Nx(VI i){auto[b,e]=Rg search(subrange(i,Rg end(v_)),p_);if(b!=Rg end(v_)&&Rg empty(p_))++b,++e;return{b,e};}
#define Fa IF<I,fw_i_tag,rd_t<V>,R,R>
CL S;CL I:public Fa{friend Fa;
#undef Fa
split_view*p_;VI i_;R n_;BL t_=0;
VC inc(){i_=n_.begin();if (i_!=Rg end(p_->v_)){i_=n_.end();if(i_==Rg end(p_->v_)){t_=1;n_={i_,i_};}else n_=p_->Nx(i_);} else t_=0;}
FC BL eq Crefp(I)RET(i.i_==j.i_&&i.t_==j.t_)BC rte()const RET(i_==Rg end(p_->v_)&&!t_)
public:I()=default;CEXP I(split_view&p,VI i,R n):p_(&p),i_(i),n_(n){}VI base()const RET(i_)R COP*()const RET({i_,n_.begin()})
};
#define RV rv_t<R>
public:CEXP split_view(V v,P p):v_(move(v)),p_(move(p)){}CEXP split_view(V v,RV p):v_(move(v)),p_(move(Vw single(p))){}
CEXP I begin()RET({*this,Rg begin(v_),Nx(Rg begin(v_))})
CEXP auto end(){if CEXP(cm_rg<V>)RET(I{*this,Rg end(v_),{}})else RET(df)}
};
TP<CL R,CL P>split_view(R&&,P&&)->split_view<Vw all_t<R>, Vw all_t<P>>;
TP<CL R>split_view(R&&,RV)->split_view<Vw all_t<R>, single_view<RV>>;
NP views {
IC ST split_fn{
TP<CL E,CL F>auto COP ()(E&&e,F&&f) const DCLT_RET(split_view {FWD(e),FWD(f)})
TP<CL F>ST fn {
F f;
TP<CL R>auto COP ()(R&&r) const DCLT_RET( split_view {FWD(r),move(f)} )
TP<CL R>auto FCOP |(R&&r,fn a) DCLT_RET( a(FWD(r)))
};
TP<CL F>auto COP ()(F&&f) const { return fn<F>{FWD(f)}; }
} split;
}
#undef RV
//[range.reverse.view]
TP<CL V>ST reverse_view:view_interface<reverse_view<V>>{
private:
TP<BL X=1>using RI=enable_if_t<X,reverse_iterator<i_t<V>>>;
TP<CL T>using RS=enable_if_t<sz_rg<T>,rd_t<T>>;
public:
CEXP explicit reverse_view(V v) : v_(move(v)){}
CEXP V base()const& { return v_; }
TP<CL VV=V>RI<>CEXP begin() { return make_reverse_iterator(Rg next(::begin(v_),::end(v_))); }
TP<CL VV=V>RI<range<const VV>>CEXP begin() const 
{ return make_reverse_iterator(Rg next(::begin(v_),::end(v_))); }
TP<CL VV=V>RI<>CEXP end() { return make_reverse_iterator(::begin(v_)); }
TP<CL VV=V>RI<range<const VV>>CEXP end() const { return make_reverse_iterator(::begin(v_)); }
TP<CL VV=V>RS<VV>CEXP size() { return ::size(v_); }
TP<CL VV=V>RS<const VV>CEXP size() const { return ::size(v_); }
private: V v_;
};
TP<CL T>reverse_view(T&&)->reverse_view<Vw all_t<T>>;
NP views {
IC ST reverse_view_fn {
TP<CL R>auto COP ()(R&&r) const RET( reverse_view {FWD(r)} )
TP<CL R>auto FCOP |(R&&r,reverse_view_fn f) RET( f(FWD(r)) ) 
} reverse;
}
//[alg.find]
IC ST find_if_fn {
TP<CL I,CL S,CL Pr,CL P>static CEXP I impl(I f,S l,Pr pr,P p){for(;f!=l;++f)if(invoke(pr,invoke(p,*f)))break;return f;}
} find_if;
IC ST find_if_not_fn{
TpReq(CL R,CL Pr,CL P=identity)(ip_rg<R>) 
auto COP()(R&&r,Pr pr,P p={})const RET(find_if_fn::impl(begin(r),end(r),not_fn(ref(pr)),ref(p)))
} find_if_not;
//[range.take.while]
TpReq(CL V,CL P)(ip_rg<V>&&is_object_v<P>/*&&indirect_unary_predicate<const P,i_t<V>>*/)
CL drop_while_view : public view_interface<drop_while_view<V,P>>{
V v_;
copyable_box<P>p_;
public:
drop_while_view(V v,P p):v_(move(v)),p_(move(p)){}
CEXP auto begin() RET(Rg find_if_not(v_,cref(*p_)))
CEXP auto end() RET(Rg end(v_))
LazyT(V,copy_constructible<V>) CEXP V base() const& RET(v_)
CEXP V base()&&RET(move(v_))
};
NP views {
IC ST drop_while_fn {
TP<CL E,CL F>auto COP ()(E&&e,F&&f) const DCLT_RET(drop_while_view {FWD(e),FWD(f)})
TP<CL F>ST fn {
F f;
TP<CL R>auto COP ()(R&&r) const DCLT_RET( drop_while_view {FWD(r),move(f)} )
TP<CL R>auto FCOP |(R&&r,fn a) DCLT_RET( a(FWD(r)) )
};
TP<CL F>auto COP ()(F&&f) const { return fn<F>{FWD(f)}; }
} drop_while;
}
//[range.view.zip]
//[zip.helper]
template<class...A>using tuple_or_pair=tuple<A...>;
TP<CL... R>concept czip=(sizeof...(R)==1&&(cm_rg<R>&&...))||(!(bd_rg<R>&&...)&&(cm_rg<R>&&...))||((ra_rg<R>&&sz_rg<R>)&&...);
TP<CL F,CL Tp>CEXP auto tfe_(F&&f,Tp&&tp) { apply([&](auto&&...a){ (invoke(f,FWD(a)),...); },FWD(tp) ); }
TP<CL F,CL Tp>CEXP auto ttf_(F&&f,Tp&&tp) 
RET(apply([&](auto&&...a)RET(tuple_or_pair<invoke_result_t<F&,decltype(a)>...>(invoke(f,FWD(a))...)),FWD(tp)))
TP<CL F,CL L,CL R,size_t... i>CEXP auto tpt_impl(F&&f,L&&l,R&&r,index_sequence<i...>)
RET(tuple_or_pair<decltype(invoke(FWD(f),get<i>(FWD(l)),get<i>(FWD(r))))...>(invoke(FWD(f),get<i>(FWD(l)),get<i>(FWD(r)))...))
TP<CL F,CL L,CL R>CEXP auto ttf_(F&&f,L&&l,R&&r)
RET(tpt_impl(FWD(f),FWD(l),FWD(r),make_index_sequence<tuple_size_v<remove_cvref_t<L>>>{}))
TP<CL F,CL L,CL R,size_t... i>VC tpf_impl(F&&f,L&&l,R&&r,index_sequence<i...>)
RET((invoke(FWD(f),get<i>(FWD(l)),get<i>(FWD(r))),...))
TP<CL F,CL L,CL R>CEXP auto tfe_(F&&f,L&&l,R&&r)
RET(tpf_impl(FWD(f),FWD(l),FWD(r),make_index_sequence<tuple_size_v<remove_cvref_t<L>>>{}))
TP<CL... V>CL zip_view:public view_interface<zip_view<V...>>{
#define MCV maybe_const<C,V>
#define TMCV(Name) tuple_or_pair<Name<MCV>...>
#define All_(...) (__VA_ARGS__##_rg<MCV>&&...)
static_assert(sizeof...(V)>0 &&((view<V>&&ip_rg<V>) &&...));
tuple<V...>v_;
TP<BL>CL S;
TP<BL C>using Tg=conditional_t<All_(ra),ra_i_tag,conditional_t<All_(bd),
bd_i_tag,conditional_t<All_(fw),fw_i_tag,ip_i_tag>>>;
TP<BL C>using D=common_type_t<rd_t<MCV>...>;
#define F IF<I<C>,Tg<C>,D<C>,TMCV(rv_t),TMCV(rr_t)>
TP<BL C>ST I:F{
TP<BL>friend ST S;friend F;I()=default;CEXP I(TMCV(i_t) i_):i_(move(i_)){}
#undef F
#define CurLazy(...) LazyV(sizeof...(V),__VA_ARGS__)
CurLazy(C&&(convertible_to<i_t<V>,i_t<MCV>>&&...))CEXP I(I<!C>i) : i_(move(i.i_)) {}
auto COP*()const RET(ttf_([](auto&i)->DCLT(auto)RET(*i),i_))
void FC iter_move(const I&i)RET(ttf_(Rg iter_move,i.i_))
CurLazy((ind_sw<i_t<MCV>>&&...))void FC iter_swap Crefp(I){tfe_(Rg iter_swap,i.i_,j.i_);}
private:TMCV(i_t)i_;
VC inc(){tfe_([](auto&i){++i;},i_);}CurLazy(1)void dec(){tfe_([](auto& i){--i;},i_);}
CurLazy(1)void adv(D<C>n){tfe_([n](auto&i){i+=n;},i_);}
CurLazy((equality_comparable<i_t<MCV>>&&...))BL FC eq Crefp(I){if CEXP(All_(bd))RET(i.i_==j.i_)else
RET(apply([](auto...b)RET((b||...)),ttf_([](auto&i,auto&j)RET(i==j),i.i_,j.i_)))}
CurLazy(1)BL FC lt Crefp(I)RET(i.i_<j.i_)
CurLazy(1)D<C>FC dif Crefp(I)RET(apply([](auto... b) RET(min({(D<C>)b...},{},abs)),ttf_([](auto&i,auto&j)RET(i-j),i.i_,j.i_)))
#undef All_
};

TP<BL C>ST S:SF<S<C>>{
friend SF<S<C>>;
S()=default;S(TMCV(s_t) s_):s_(move(s_)){}
CurLazy(C&&(convertible_to<s_t<V>,s_t<MCV>>&&...))CEXP S(S<!C>i):s_(i.s_){}
private:TMCV(s_t)s_;
#define Def(Name) TpReq(BL CC)((Name##sentinel_for<s_t<MCV>,i_t<maybe_const<CC,V>>>&&...))CEXP
Def()BL eq(const I<CC>&i)const RET(apply([](auto...b) RET((b||...)),ttf_([](auto&i,auto&j)RET(i==j),i.i_,s_)))
Def(sized_)auto dif(const I<CC>&i)const
RET(apply([](auto...b)RET(Rg min({(id_t<I<CC>>)b...},{},Rg abs)),ttf_([](auto&i,auto&j)RET(i-j),s_,i.i_)))
#undef Def
};
#undef TMCV
#undef MCV
public:
zip_view(V...v):v_(move(v)...){}
CurLazy(!(simple_view<V>&&...))CEXP I<0>begin()RET(ttf_(Rg begin,v_))
CurLazy((range<const V>&&...)) CEXP I<1>begin()const RET(ttf_(Rg begin,v_))
CurLazy(!(simple_view<V>&&...)) CEXP auto end() {
if CEXP(!czip<V...>) return S<0>(ttf_(Rg end,v_));
else if CEXP((ra_rg<V>&&...)) return begin() + size();
else return I<0>(ttf_(Rg end,v_));
}
CurLazy((range<const V>&&...)) CEXP auto end()const{
if CEXP(!czip<const V...>) return S<0>(ttf_(Rg end,v_));
else if CEXP((ra_rg<const V>&&...)) return begin() + size();
else return I<0>(ttf_(Rg end,v_));
}
CurLazy((sz_rg<V>&&...)) auto CEXP size()
RET(apply([](auto...a)RET(Rg min({(make_unsigned_t<common_type_t<DCLT(a)...>>)a...})),ttf_(Rg size,v_)))
CurLazy((sz_rg<const V>&&...)) auto CEXP size() const
RET(apply([](auto...a)RET(Rg min({(make_unsigned_t<common_type_t<DCLT(a)...>>)a...})),ttf_(Rg size,v_)))
#undef CurLazy
};
TP<CL... R>zip_view(R&&...)->zip_view<Vw all_t<R>...>;
NP views {
IC ST zip_fn {
TP<CL... R>auto COP()(R&&...r) const RET( zip_view { (R&&)r... } )
} zip;
IC ST enumerate_fn {
TP<CL... R>auto COP()(R&&... r) const NOEXP_DCLT_RET(zip(iota(0),FWD(r)...) )
TP<CL R>auto FCOP|(R&&r,enumerate_fn f)  NOEXP_DCLT_RET(f(FWD(r)))
} enumerate;
}//views
IC ST adjacent_find_fn{
TP<CL I,CL S,CL Pr,CL P>CEXP static I impl(I f,S l,Pr pr,P p){
if(f==l)RET(f)auto w=proj_cmp(ref(pr),ref(p));
for(auto n=next(f);n!=l;++n,++f)if(w(*f,*n))break;return f;
}
TpReq(CL R,CL C=equal_to<>,CL P=identity)(fw_rg<R>&&ind_bp<C,projected<i_t<R>,P>>)
auto COP()(R&&r,C c={},P p={})const RET(impl(ALL(r),ref(c),ref(p)))
TpReq(CL I,CL S,CL C=equal_to<>,CL P=identity)(fw_i<I>&&sentinel_for<S,I>&&ind_bp<C,projected<I,P>>)
auto COP()(I f,S l,C c={},P p={})const RET(impl(move(f),move(l),ref(c),ref(p)))
} adjacent_find;
//[views.chunk_by][advance_3]
TpReq(CL V,CL P)(fw_rg<V>&&is_object_v<P>&&ind_bp<P,i_t<V>,i_t<V>>)CL chunk_by_view:public view_interface<chunk_by_view<V,P>>{
V v_;copyable_box<P>p_;
using VI=i_t<V>;
CEXP VI Nx(VI i)RET(Rg next(Rg adjacent_find(i,Rg end(v_),not_fn(ref(*p_))),1,Rg end(v_)))
LazyT(V,1)CEXP VI Pv(VI i)RET(Rg prev(Rg adjacent_find(reverse_view(subrange(Rg begin(v_),i)),not_fn(flip(ref(*p_))).base(),1,Rg begin(v_))))
using R=subrange<VI>;using Tg=conditional_t<bd_rg<V>,bd_i_tag,fw_i_tag>;
#define F IF<I,Tg,rd_t<V>,R,R>
CL I:public F{
friend F;chunk_by_view*p_;VI i_,n_;
#undef F
VC inc(){i_=n_,n_=p_->Nx(i_);}LazyT(V,1)VC dec(){n_=i_,i_=p_->Pv(n_);}
BL FC eq Crefp(I)RET(i.i_==j.i_)BC rte()const RET(i_==n_)
public:CEXP I()=default;CEXP I(chunk_by_view&p,VI i,VI n):p_(&p),i_(i),n_(n){}
R COP*()const RET({i_,n_})
};
public:chunk_by_view()=default;chunk_by_view(V v,P p):v_(move(v)),p_(move(p)){}
CEXP I begin()RET({*this,Rg begin(v_),Nx(Rg begin(v_))})
CEXP auto end(){if CEXP(cm_rg<V>)RET(I{*this,Rg end(v_),Rg end(v_)})else RET(df)}
};
TP<CL R,CL P>chunk_by_view(R&&,P)->chunk_by_view<Vw all_t<R>,P>;
//[view.subset]
TP<CL T>CL subset_view:public view_interface<subset_view<T>>{
#define Fa IF<I,fw_i_tag,id_t<T>,T,T>
CL I:public Fa{
friend Fa;T t,v_;
VC inc()noexcept{v_=(v_-1)&t;}
BL FC eq Crefp(I)noexcept RET(i.v_==j.v_)BC rte()const noexcept RET(v_==t)
public:I()=default;CEXP I(T t)noexcept:t(t),v_(t&(t-1)){}
T COP*() const noexcept RET(v_)
};
T t;
public:CEXP subset_view(T t) noexcept: t(t) {}
CEXP I begin()const noexcept RET( { t } )CEXP df_t end()const noexcept RET({})
auto CEXP size()const noexcept RET( to_unsigned(T{1})  << __popcount(t) )
};
Def_Adap1(subset)
TP<CL T>CL decompose_view:public view_interface<decompose_view<T>>{
T t;
ST I:public Fa{
friend Fa;T x,i;
#undef Fa
VC satisfy()noexcept{while(x%i!=0){if(i*i>x){i=x;break;}++i;}}
VC inc()noexcept{x/=i;satisfy();}
BL FC eq Crefp(I) noexcept RET(i.x==j.x&&i.i==j.i)
BL CEXP rte()const noexcept RET(x==1)
public:I()=default;CEXP I(T x)noexcept:i(2),x(x){satisfy();}
T COP*()const noexcept RET(i)
};
public:CEXP decompose_view(T t)noexcept:t(t){}
CEXP I begin() const noexcept RET({t})CEXP df_t end()const noexcept RET({})
};
Def_Adap1(decompose)
NP to_ {
TP<CL R>using proxy_iter=istream_iterator<rv_t<R>>;
TP<CL C,CL R,CL... A>auto IC impl(tag<4>,R&&r,A&&...a)DCLT_RET(C(FWD(r),FWD(a)...))
TP<CL C,CL R,CL... A>auto IC impl(tag<3>,R&&r,A&&...a)DCLT_RET(C(begin(r),end(r),FWD(a)...))
//[todo] maybe_simplify
TP<CL Ref,CL C>auto IC get_inserter(C& c,tag<1>)->DCLT(c.push_back(DCLV(Ref)),back_inserter(c)) { return back_inserter(c); }
TP<CL Ref,CL C>auto IC get_inserter(C& c,tag<0>)->DCLT(c.insert(end(c),DCLV(Ref)),inserter(c,end(c))) { return inserter(c,end(c)); }
CpDef(can_reserve,CL C)(C& c,size_t n)(
c.reserve(n),
Cret(same_as,c.max_size())(DCLT(c.size()))
Cret(same_as,c.capacity())(DCLT(c.size()))
);
TP<CL C>concept can_reserve=CpRef(can_reserve,C);
TP<CL C,CL R,CL... A>auto IC impl(tag<1>,R&&r,A&&...a)->decltype(get_inserter<rr_t<R>>(DCLV(C&),tag<1>{}),C(FWD(a)...)) {
auto c=C(FWD(a)...);
if CEXP(sz_rg<R>&&can_reserve<C>)c.reserve(size(r));
Rg copy(r,get_inserter<rr_t<R>>(c,tag<1>{}));
return c;
}
TP<TPP C,CL R,CL... A>using Cont=decltype(C(proxy_iter<R>(),proxy_iter<R>(),DCLV(A)...));
TpReq(CL C,CL R,CL...A)(range<R>)CEXP auto To(tag<1>,R&&r,A&&...a)DCLT_RET(impl<C>(tag<5>{},FWD(r),FWD(a)...))
TpReq(TPP C,CL R,CL...A)(range<R>)CEXP auto To(tag<1>,R&&r,A&&...a)DCLT_RET(impl<Cont<C,R,A...>>(tag<5>{},FWD(r),FWD(a)...))
#define Def(TMP,NAME) \
TP<TMP C,CL... A>ST NAME{tuple<A...>pa;\
TP<CL R>auto COP()(R&&r)const&->DCLT(To<C>(tag<1>{},DCLV(R),DCLV(const A&)...))\
RET(apply([&](auto&&...a)RET(To<C>(tag<1>{},(R&&)r,FWD(a)...)),pa))\
TP<CL R>auto COP()(R&&r)&&->DCLT(To<C>(tag<1>{},DCLV(R),DCLV(A)...))\
RET(apply([&](auto&&...a)RET(To<C>(tag<1>{},(R&&)r,FWD(a)...)),move(pa)))\
TpReq(CL R,CL F)(same_as<NAME,remove_cvref_t<F>>)auto FCOP|(R&&r,F&&f) DCLT_RET(FWD(f)(FWD(r)))\
};\
TP<TMP C,CL... A>CEXP auto To(tag<0>,A&&...a)RET(NAME<C,decay_t<A>...>{FWD(a)...})
Def(CL,xfn)Def(TPP,yfn)
#undef Def
}//to_
TP<CL C,CL... A>CEXP auto to(A&&...a)DCLT_RET(to_::To<C>(tag<1>{},FWD(a)...))
TP<TPP C,CL... A>CEXP auto to(A&&...a)DCLT_RET(to_::To<C>(tag<1>{},FWD(a)...))
}//ranges
NP print {
TP<CL T>ST brac{T l,r;};TP<CL T>brac(T,T)->brac<T>;TP<CL T>ST delim{T d;};TP<CL T>delim(T)->delim<T>;
TP<CL O,CL B>ST ob_br{using fmt=void;O&o;B b;};TP<CL O,CL D>ST ob_de{using fmt=void;O&o;D d;};
TP<CL B,CL D>ST br_de{B bra;D del;};TP<CL O,CL B,CL D>ST ob_dr_de{using fmt=void;O&o;B b;D d;};
TP<CL S,CL T>ST Raii{S&s;T t;Raii(S&s,T t):s(s),t(move(t)){s<<t.l;}~Raii(){s<<t.r;}};
//symbol
CPO default_brac=brac {'[',']'};CPO default_delim=delim { ',' };CPO et=delim { '\n' };CPO ebra=brac { "","" };
TP<CL O,CL B>ob_br<O,brac<B>>COP/(O&&o,brac<B>b)RET({o,b})
TP<CL O,CL D>ob_de<O,delim<D>>COP/(O&&o,delim<D>d)RET({o,d})
TP<CL B,CL D>br_de<brac<B>,delim<D>>COP/(brac<B>b,delim<D>d)RET({b,d})
TP<CL O,CL B>ob_br<O,brac<B>>COP/(brac<B>b,O&&o)RET({o,b})
TP<CL O,CL D>ob_de<O,delim<D>>COP/(delim<D>d,O&&o)RET({o,d})
TP<CL B,CL D>br_de<brac<B>,delim<D>>COP/(delim<D>d,brac<B>b)RET({b,d})
TP<CL O,CL B,CL D> ob_dr_de<O,brac<B>,delim<D>>COP/(O&&o,br_de<brac<B>,delim<D>>bd)RET({o,bd.b,bd.d})
TP<CL O,CL B,CL D> ob_dr_de<O,brac<B>,delim<D>>COP/(br_de<brac<B>,delim<D>>bd,O&&o)RET({o,bd.b,bd.d})
TP<CL O,CL B,CL D>ob_dr_de<O,brac<B>,delim<D>>COP/(ob_br<O,brac<B>>ob,delim<D>d)RET({ob.o,ob.b,d})
TP<CL O,CL B,CL D>ob_dr_de<O,brac<B>,delim<D>>COP/(delim<D>d,ob_br<O,brac<B>>ob)RET({ob.o,ob.b,d})
TP<CL O,CL B,CL D>ob_dr_de<O,brac<B>,delim<D>>COP/(ob_de<O,delim<D>>od,brac<B>b)RET({od.o,b,od.d})
TP<CL O,CL B,CL D>ob_dr_de<O,brac<B>,delim<D>>COP/(brac<B>b,ob_de<O,delim<D>>od)RET({od.o,b,od.d})
TP<CL T>DCLT(auto)fmt(T&&t){
if CEXP(is_convertible_v<T,string_view>)RET(quoted(string_view(t)))
else if CEXP(is_same_v<decay_t<T>,char>)RET(quoted(string_view{&t,1},'\''))else RET(FWD(t))
}
TP<CL S,CL D>CEXP S&put_delim(S&s,BL f,D d){if(!f)s<<d.d<<' ';return s;}
CpDef(has_del,CL T)(T t)(t.d,);TP<CL T>concept has_del=CpRef(has_del,T);
CpDef(has_bra,CL T)(T t)(t.b,);TP<CL T>concept has_bra=CpRef(has_bra,T);
//decl
TP<CL S>void impl(S&, const string&,tag<6>)=delete;
TP<CL S, size_t N>void impl(S&, const char(&)[N], tag<6>)=delete;
TP<CL S,TPP W,CL R,CL...Re,CL=Req(Rg range<R>),CL=void_t<TY W<R,Re...>::fmt>>void impl(S&s,W<R,Re...>,tag<3>);
TP<CL S,TPP W,CL T,CL...Re,CL=TY tuple_size<remove_cvref_t<T>>::type,CL=void_t<TY W<T,Re...>::fmt>>
void impl(S&,W<T,Re...>w,tag<2>);
TP<CL S,CL R,CL=Req(Rg range<R>)>void impl(S&s,R&&r,tag<1>);
TP<CL S,CL T,CL=TY tuple_size<remove_cvref_t<T>>::type>void impl(S&s,T&&t,tag<0>);
//op
TP<CL Ch,CL Tr,CL T>auto operator<<(basic_ostream<Ch,Tr>&s,T&&t)DCLT_RET(impl(s,t,tag<6>{}),s)
//impl
#define DEF auto d=[&]{if CEXP(has_del<WW>)return w.d;else return default_delim;};auto b=[&]{if CEXP(has_bra<WW>)return w.b;else return default_brac;};
#define MSeq make_index_sequence<tuple_size_v<remove_cvref_t<T>>>{}
TP<CL S,CL T,CL B,CL D,size_t... I>
void T_impl(S&s,T&&t,index_sequence<I...>,B b,D d){Raii _{s,b};((put_delim(s,I==0,d)<<fmt(get<I>(t))),...);  }
TP<CL S,CL R,CL B,CL D>void R_impl(S&&s,R&&r,B b,D d){Raii _{s,b};size_t i=0;for(auto&&e:r)put_delim(s,++i==1,d)<<fmt(e);}
TP<CL S,TPP W,CL R,CL...Re,CL,CL>void impl(S&s,W<R,Re...> w,tag<3>){using WW=W<R,Re...>;DEF R_impl(s,w.o,b(),d());}
TP<CL S,TPP W,CL T,CL...Re,CL,CL>void impl(S&s,W<T,Re...>w,tag<2>){using WW=W<T,Re...>;DEF T_impl(s,w.o,MSeq,b(),d());}
TP<CL S,CL R,CL>void impl(S&s,R&&r,tag<1>){R_impl(s,FWD(r),default_brac,default_delim);}
TP<CL S,CL T,CL>void impl(S&s,T&&t,tag<0>){T_impl(s,t,MSeq,default_brac,default_delim);}
#undef MSeq
#undef DEF
}//print
using print::operator<<,print::et,print::ebra;
NP safe {
#define DEF using T=remove_reference_t<TT>;using U=remove_reference_t<UU>;
static CEXP int ulp=2;
TP<CL... T>using limits=numeric_limits<common_type_t<T...>>;
TP<CL TT,CL UU>IC BL eq(TT&&t,UU&&u){DEF
if CEXP(is_integral_v<T>&&is_integral_v<U>)
{if CEXP(is_signed_v<T> ==is_signed_v<U>)RET(t==u)else if CEXP(is_signed_v<T>)RET(t<0?0:to_unsigned(t)==u)else RET(u<0?0:t==to_unsigned(u))}
else if CEXP(is_floating_point_v<U>||is_floating_point_v<T>){auto x=abs(t-u); return x<=limits<T,U>::epsilon()*ulp || x<limits<T,U>::min();}
else RET(t==u)
}
TP<CL TT,CL UU>IC BL lt(TT&&t,UU&&u){DEF
if CEXP(is_integral_v<T>&&is_integral_v<U>)
{ if CEXP(is_signed_v<T> ==is_signed_v<U>)RET(t<u)else if CEXP(is_signed_v<T>)RET(t<0?1:to_unsigned(t)<u)else RET(u<0?0:t<to_unsigned(u))}
else if CEXP(is_floating_point_v<T>||is_floating_point_v<U>)RET(eq(t,u)?0:t<u)
else return t<u;
}
#undef DEF
TP<CL T>CL sf { 
T v={};
public:
sf()=default; TP<CL U>CEXP sf(U&&x) : v(FWD(x)) {}
COP T() const { return v; }
};
TP<CL T>sf(T)->sf<T>; inline sf<ull>COP ""_sf(ull x) { return x; }
inline sf<long double>COP ""_sf(long double x) { return x; }

#define DefP(OP,Proxy) \
TP<CL L,CL R>BL COP OP(sf<L>const& l,sf<R>const& r) RET(Proxy(L(l),R(r))) \
TP<CL L,CL R>BL COP OP(L const& l,sf<R>const& r) RET(Proxy(l,R(r))) \
TP<CL L,CL R>BL COP OP(sf<L>const& l,R const& r) RET(Proxy(L(l),r))
DefP(==,eq) DefP(<,lt)
#undef DefP 
#define DefP(OP,...) \
TP<CL L,CL R>BL COP OP(sf<L>const&l,sf<R>const& r) RET(__VA_ARGS__) \
TP<CL L,CL R>BL COP OP(L const&l,sf<R>const& r) RET(__VA_ARGS__) \
TP<CL L,CL R>BL COP OP(sf<L>const&l,R const& r) RET(__VA_ARGS__)
DefP(>,r<l) DefP(<=,!(r<l)) DefP(>=,!(l<r)) DefP(!=,!(l==r))
#undef DefP
}
using safe::sf;

inline NP numbers {
IC long MOD=998244353;
TP<CL T>IC auto e_v=static_cast<T>(2.71828182845904523542816810799394033892895095050334930419921875);
TP<CL T>IC auto pi_v=static_cast<T>(3.14159265358979323851280895940618620443274267017841339111328125);
TP<CL T>IC auto inf_v=static_cast<T>(0x3f3f3f3f3f3f3f3fl);
IC double e=e_v<double>;
IC double pi=pi_v<double>;
IC int inf=inf_v<int>;
}
TP<auto M=int64_t(1e9+7)>ST B{
using L=decltype(M);L v;
B()=default;CEXP B(L x):v((x%=M)<0?x+=M:x){}
using X=B&;TP<CL...T>using Q=enable_if_t<(integral<T>&&...),B>;
TpReq(CL I)(integral<I>&&!same_as<int,I>) explicit COP I()const{return I(v);}COP int()const{return int(v);}
X COP+=(B r)RET_THIS(v-=M-r.v;if(v<0)v+=M;)X COP-=(B r)RET_THIS(v-=r.v;if(v<0)v+=M;)
X COP*=(B r)RET_THIS((v+=r.v)%=M;)X COP/=(B r)RET(*this*=r.inv();)
#define Def(OP,OPE) B FCOP OP(B l,B r)RET(l OPE r)TP<CL I>Q<I>FCOP OP (I l,B r)RET((B)l OPE r)TP<CL I>Q<I>FCOP OP (B l,I r)RET(l OPE r)
Def(+,+=)Def(-,-=)Def(*,*=)Def(/,/=)
#undef Def
B COP+()const RET_THIS()B COP-()const RET(0-*this)X COP++()RET(*this+=1)X COP--()RET(*this-=1)
TP<CL I>Q<I>CEXP pow(I r)const{B b=*this,x=1;while(r){if(r&1)x*=b;b*=b;r/=2;}return x;}TP<CL I>Q<I>FC pow(B l,I r)RET(l.pow(r))
TP<CL L,CL R>Q<L,R>static CEXP pow(L l,R r)RET(B(l).pow(r))FC B inv(B x)RET(x.inv())CEXP B inv()const RET(pow(M-2))
TP<CL I>Q<I>static fac(I r){static unordered_map<I,B>f{{0,1}};if(auto i=f.find(r);i!=end(f))return i->second;return f[r]=r*fac(r-1);}
TP<CL I>Q<I>static comb(I x,I y)RET(fac(x)/fac(y)/fac(x-y))
};
TP<auto M>using basic_mod=B<M>;using mod=B<>;using modint=B<int(1e9+7)>;inline mod COP ""_m(ull x)RET(mod(x))
inline NP unionfind {
CL UF {
vector<int>fa,sz;
size_t n,comp_cnt;
public:
UF(size_t n): n(n),comp_cnt(n),fa(n),sz(n,1) {
iota(begin(fa),end(fa),0);
}
auto size() { return n; }
auto count() { return comp_cnt; }
int findset(int x) { return fa[x]==x ? x : fa[x]=findset(fa[x]); }
void unite(int x,int y) {
if (sz[x]<sz[y]) swap(x,y);
fa[y]=x;
sz[x] += sz[y];
--comp_cnt;
}
BL findAndUnite(int x,int y) {
int x0=findset(x),y0=findset(y);
if (x0!=y0) unite(x0,y0);
return x0!=y0;
}
};
}
inline NP utility {
CpDef(can_top,CL T)(T& t)(t.top(),);
CEXP auto pop=[](auto& t) {
using T=decay_t<decltype(t)>;auto r=move((TY T::value_type&)[&]()->auto&&{if CEXP(CpRef(can_top,T))RET(t.top())else RET(t.front())}());
t.pop();return r;
};
}//utility
inline NP direction {
CEXP int dir [][2] { {0,1},{1,0},{0,-1},{-1,0} };
CEXP int dir8[][2] { {0,1},{1,0},{0,-1},{-1,0},{1,1},{-1,1},{1,-1},{-1,-1} };
CEXP auto valid=[](auto m,auto n)RET([=](size_t x,size_t y)RET(x<m&&y<n));
}
#ifdef __cpp_lib_memory_resource
IC auto set_pmr=[] {
static byte buffer [1 << 30];
static auto pool=pmr::monotonic_buffer_resource { data(buffer),size(buffer) };
set_default_resource(&pool);
return 0;
};
#endif
IC auto set_fast_io=[]{ios::sync_with_stdio(0); cin.tie(nullptr); cout.tie(nullptr); cout << setprecision(12); return 0;};
}//my
TP<CL... A>VC swap(const tuple<A...>& i,const tuple<A...>& j){Rg tfe_(Rg swap,i,j);}
TP<CL>concept is_vv=0;TP<CL T>concept is_vv<vector<T>> =1;
TP<CL T>ST tuple_size<vector<T>>:integral_constant<size_t,vector_size_v>{};
TP<size_t I,CL T>ST tuple_element<I,vector<T>>:enable_if<1,T>{};
TpReq(size_t I,CL T)(is_vv<remove_cvref_t<T>>)DCLT(auto)get(T&&t)RET(FWD(t)[I])
}//std
inline NP simplify {
#define Yc Y_combinator
NP views=Rg views;using Rg to;
CPO fac=Vw decompose; CPO subset=Vw subset;
CPO range=Vw iota; CPO zip=Vw zip; CPO enu=Vw enumerate; CPO split=Vw split;
CPO rev=Vw reverse; CPO tran=Vw transform;CPO single=Vw single;//CPO chunk_by=Vw chunk_by;
}//simplify
