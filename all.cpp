#include <bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
inline constexpr size_t vector_size_v=2;
#define NP namespace
using NP std;
NP std {
#define debug(...) cout << #__VA_ARGS__ << "\t" << forward_as_tuple(__VA_ARGS__)/ebra << endl;
#define ALL(...) begin(__VA_ARGS__),end(__VA_ARGS__)
#define FWD(...) static_cast<DCLT(__VA_ARGS__)&&>(__VA_ARGS__)
#define DCLV(...) declval<__VA_ARGS__>()
#define NOEXP(...) noexcept(noexcept(__VA_ARGS__))
#define DCLT decltype
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
#define FC friend CEXP
#define VC void CEXP
#define BC BL CEXP
#define SC static CEXP
#define AC auto CEXP
#define FAC friend AC
#define SAC static AC
#define COP CEXP operator
#define FCOP friend CEXP operator
#define NUA [[__no_unique_address__]]

#define CPO CEXP inline auto
#define concept IC BL
#define Rg ranges::
#define Vw views::

#define In_Vws(...) NP views{__VA_ARGS__}
#define In_Rgs(...) NP ranges{__VA_ARGS__}
#define In_cpo(...) inline NP cpo{__VA_ARGS__}

#define Req(...) requires_expr<__VA_ARGS__>
#define ReqExpr(...) boolT<1,DCLT(__VA_ARGS__)>
#define ReqType(...) boolT<1,__VA_ARGS__>
#define TpReqt(...) Req(__VA_ARGS__)=0>
#define TpReq(...) TP< __VA_ARGS__ ,TpReqt

#define LazyT(T,...) TP<CL t=T,Req(boolT<1,t>&&(__VA_ARGS__))=0>
#define LazyV(V,...) TP<auto v=V,Req(boolV<1,v>&&(__VA_ARGS__))=0>

#define Reqs(...) Req(__VA_ARGS__) {},
#define ImplRetReq(...) __VA_ARGS__ )>>{},
#define RetReq0(ConceptName) requires_expr< ConceptName<DCLT( ImplRetReq
#define RetReq(ConceptName,...) requires_expr< ConceptName<__VA_ARGS__,DCLT( ImplRetReq

#define CpDef(NAME,...) ST NAME##_concept { TP<__VA_ARGS__>auto freq ImplCpDef0
#define ImplCpDef0(...) (__VA_ARGS__)->DCLT ImplCpDef1
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
#define MakeAuto(Na,...) Na<decay_t<DCLT(__VA_ARGS__)>>(__VA_ARGS__)
//[traits]
#define rmv_r_t remove_reference_t

#define TypeInner(In,__VA_ARGS__) TY rmv_cvr_t<__VA_ARGS__>::In

TP<CL T>ST ty_id{using type=T;};
TP<CL T>using ty_id_t=TY ty_id<T>::type;
TP<CL T>ST remove_cvref:remove_cv<rmv_r_t<T>>{};
TP<CL T>using rmv_cvr_t=TY remove_cvref<T>::type;
TP<CL T,CL>ST like:ty_id<T>{};
#define F(FL) TP<CL T,CL U>ST like<T,U FL>:ty_id<T FL>{};
F(&)F(&&)F(const)F(const&)F(const&&)
#undef F
TP<CL T,CL U>using like_t=TY like<rmv_cvr_t<T>,U>::type;
#define limits numeric_limits
using ull=unsigned long long;
using lll=__int128;
using ulll=unsigned __int128;
TP<>ST is_integral<lll>:true_type{};
TP<>ST is_integral<ulll>:true_type{};
TP<>ST make_signed<lll>:ty_id<lll>{};
TP<>ST make_signed<ulll>:ty_id<lll>{};
TP<>ST make_unsigned<lll>:ty_id<ulll>{};
TP<>ST make_unsigned<ulll>:ty_id<ulll>{};

inline NP my{
NP pbds_{using NP __gnu_pbds;TP<CL T,CL V=null_type,CL C=less<>>using order_tree=tree<T,V,C,rb_tree_tag,tree_order_statistics_node_update>;}
using pbds_::order_tree;
ST __empty{};
//[requires_]
TP<CL,CL...>auto _req_impl(...)->false_type;TP<CL R,CL... A,CL=DCLT(&R::TP freq<A...>)>auto _req_impl(int)->true_type;
TP<CL R,CL... A>IC BL requires_=DCLT(_req_impl<R,A...>(0))::value;
TP<BL B,CL...>IC BL boolT=B; TP<BL B,auto...>IC BL boolV=B;
TP<BL E,CL T=int>using requires_expr=enable_if_t<E,T>;

TP<size_t I>ST tag:tag<I-1>{};TP<>ST tag<0>{};

//[common.reference]
TP<TPP AliasT,CL... A>auto exists_helper(...)->false_type;
TP<TPP AliasT,CL... A,CL=AliasT<A...>>auto exists_helper(int)->true_type;
TP<TPP AliasT,CL... A>
IC BL exists_v=DCLT(exists_helper<AliasT,A...>(0))::value;
NP common_detail { 
TP<CL...>ST common_type;
TP<CL T,CL U>ST copy_cv:ty_id<U>{};
TP<CL T,CL U>ST copy_cv<const T,U>:ty_id<add_const_t<U>>{};
TP<CL T,CL U>ST copy_cv<volatile T,U>:ty_id<add_volatile_t<U>>{};
TP<CL T,CL U>ST copy_cv<const volatile T,U>:ty_id_t<add_cv_t<U>>{};
TP<CL T,CL U>using copy_cv_t=TY copy_cv<T,U>::type;
TP<CL T>using cref_t=add_lvalue_reference_t<const rmv_r_t<T>>;
TP<CL T,CL U>using cond_res_t=DCLT(1? DCLV(T(&)())():DCLV(U(&)())());
//For some value of "simple"
TP<CL A,CL B,CL=rmv_r_t<A>,CL=rmv_r_t<B>,CL=void>ST common_ref {};
TP<CL A,CL B>using common_ref_t=TY common_ref<A,B>::type;
TP<CL A,CL B,CL=rmv_r_t<A>,CL=rmv_r_t<B>,CL=void>ST lval_common_ref {};
TP<CL A,CL B,CL X,CL Y>
ST lval_common_ref<A,B,X,Y,enable_if_t<is_reference_v<cond_res_t<copy_cv_t<X,Y>&,copy_cv_t<Y,X>&>>>>
{ using type=cond_res_t<copy_cv_t<X,Y>&,copy_cv_t<Y,X>&>; };
TP<CL A,CL B>using lval_common_ref_t=TY lval_common_ref<A,B>::type;
TP<CL A,CL B,CL X,CL Y>ST common_ref<A&,B&,X,Y>:lval_common_ref<A&,B&>{};
TP<CL X,CL Y>using rref_cr_helper_t=rmv_r_t<lval_common_ref_t<X&,Y&>>&&;
TP<CL A,CL B,CL X,CL Y>ST common_ref<A&&,B&&,X,Y,enable_if_t<
is_convertible_v<A&&,rref_cr_helper_t<X,Y>>&&is_convertible_v<B&&,rref_cr_helper_t<X,Y>>>>
{ using type=rref_cr_helper_t<X,Y>; };
TP<CL A,CL B,CL X,CL Y>ST common_ref<A&&,B&,X,Y,enable_if_t<
is_convertible_v<A&&,lval_common_ref_t<const X&,Y&>>>>
{ using type=lval_common_ref_t<const X&,Y&>; };
TP<CL A,CL B,CL X,CL Y>ST common_ref<A&,B&&,X,Y>:common_ref<B&&,A&>{};
TP<CL>ST xref { TP<CL U>using type=U; };
TP<CL A>ST xref<A&>{ TP<CL U>using type=add_lvalue_reference_t<TY xref<A>::TP type<U>>; };
TP<CL A>ST xref<A&&>{ TP<CL U>using type=add_rvalue_reference_t<TY xref<A>::TP type<U>>; };
TP<CL A>ST xref<const A>{ TP<CL U>using type=add_const_t<TY xref<A>::TP type<U>>; };
TP<CL A>ST xref<volatile A>{ TP<CL U>using type=add_volatile_t<TY xref<A>::TP type<U>>; };
TP<CL A>ST xref<const volatile A>{ TP<CL U>using type=add_cv_t<TY xref<A>::TP type<U>>; };
TP<CL T,CL U,TP<CL>CL TQual,TP<CL>CL UQual>ST basic_com_ref {};
TP<CL...>ST com_ref;
TP<CL... Ts>using com_ref_t=TY com_ref<Ts...>::type;
TP<>ST com_ref<>{};
TP<CL T0>ST com_ref<T0>{ using type=T0; };
TP<CL T,CL U>IC BL has_common_ref_v=exists_v<common_ref_t,T,U>;
TP<CL T,CL U>using basic_common_ref_t=TY basic_com_ref<rmv_cvr_t<T>,rmv_cvr_t<U>,
xref<T>::TP type,xref<U>::TP type>::type;
TP<CL T,CL U>IC BL has_basic_common_ref_v=exists_v<basic_common_ref_t,T,U>;
TP<CL T,CL U>IC BL has_cond_res_v=exists_v<cond_res_t,T,U>;
TP<CL T,CL U,CL=void>ST binary_common_ref:common_type<T,U>{};
TP<CL T,CL U>ST binary_common_ref<T,U,enable_if_t<has_common_ref_v<T,U>>>:common_ref<T,U>{};
TP<CL T,CL U>ST binary_common_ref<T,U,enable_if_t<has_basic_common_ref_v<T,U>&&!has_common_ref_v<T,U>>>
{ using type=basic_common_ref_t<T,U>; };
TP<CL T,CL U>
ST binary_common_ref<T,U,enable_if_t<has_cond_res_v<T,U>&&!has_basic_common_ref_v<T,U>&&!has_common_ref_v<T,U>>>
{ using type=cond_res_t<T,U>; };
TP<CL T1,CL T2>ST com_ref<T1,T2>:binary_common_ref<T1,T2>{ };
TP<CL Void,CL T1,CL T2,CL...Re>ST multiple_com_ref {};
TP<CL T1,TY T2,CL...Re>ST multiple_com_ref
<void_t<com_ref_t<T1,T2>>,T1,T2,Re...>:com_ref<com_ref_t<T1,T2>,Re...>{};
TP<CL T1,CL T2,CL... R>ST com_ref<T1,T2,R...>:multiple_com_ref<void,T1,T2,R...>{};
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
TP<CL T>ST common_type<T>:common_type<T,T>{};
TP<CL T,CL U>ST common_type<T,U>:binary_common_type<T,U>{};
TP<CL Void,CL...>ST multiple_common_type {};
TP<CL T1,CL T2,CL...R>ST multiple_common_type<void_t<common_type_t<T1,T2>>,T1,T2,R...>
:common_type<common_type_t<T1,T2>,R...>{};
TP<CL T1,CL T2,CL... R>ST common_type<T1,T2,R...>:multiple_common_type<void,T1,T2,R...>{};
}//common_detail
using common_detail::com_ref;
using common_detail::com_ref_t;

//[invoke]
NP invoke_{
TP<CL>CEXP BL isRW=0;
TP<CL T>CEXP BL isRW<reference_wrapper<T>> =1;
TpReq(CL B,CL T,CL D,CL... A)(is_function_v<T>&&is_base_of_v<B,decay_t<D>>)
AC impl(T B::*f,D&&r,A&&...a)NOEXP_DCLT_RET((FWD(r).*f)(FWD(a)...))
TpReq(CL B,CL T,CL R,CL... A)(is_function_v<T>&&isRW<decay_t<R>>)
AC impl(T B::*f,R&&r,A&&...a)NOEXP_DCLT_RET((r.get().*f)(FWD(a)...))
TpReq(CL B,CL T,CL P,CL... A)(is_function_v<T>&&!isRW<decay_t<P>>&&!is_base_of_v<B,decay_t<P>>)
AC impl(T B::*f,P&&p,A&&...a)NOEXP_DCLT_RET(((*FWD(p)).*f)(FWD(a)...))
TpReq(CL B,CL T,CL D)(is_function_v<T>&&is_base_of_v<B,decay_t<D>>)
AC impl(T B::*d,D&&r)NOEXP_DCLT_RET(FWD(r).*d)
TpReq(CL B,CL T,CL R)(!is_function_v<T>&&isRW<decay_t<R>>)
AC impl(T B::*d,R&&r)NOEXP_DCLT_RET(r.get().*d)
TpReq(CL B,CL T,CL P)(!is_function_v<T>&&!isRW<decay_t<P>>&&!is_base_of_v<B,decay_t<P>>)
AC impl(T B::*d,P&&p)NOEXP_DCLT_RET((*FWD(p)).*d)
TpReq(CL F,CL... A)(!is_member_pointer_v<decay_t<F>>)
AC impl(F&&f,A&&...a)NOEXP_DCLT_RET(FWD(f)(FWD(a)...))
ST fn { TP<CL F,CL... A>auto COP()(F&&f,A&&...a)const NOEXP_DCLT_RET(impl(FWD(f),FWD(a)...)) };
}//invoke_
In_Rgs(In_cpo(IC invoke_::fn invoke;))
TP<CL Void,CL,CL...>ST invoke_result_helper {};
TP<CL F,CL... A>
ST invoke_result_helper<void_t<DCLT(Rg invoke(DCLV(F),DCLV(A)...))>,F,A...>{
using type=DCLT(Rg invoke(DCLV(F),DCLV(A)...));
};
TP<CL F,CL... A>ST invoke_result:invoke_result_helper<void,F,A...>{};
TP<CL F,CL... A>using inv_res_t=TY invoke_result<F,A...>::type;
//[concept.invocable]
ST invocable_concept {
#if (defined(__clang_major__) &&(defined(__apple_build_version__) ||__clang_major__<7))
TP<CL F,CL... A>auto freq(F&&f,A&&...a)->inv_res_t<F,A...>;
#else
TP<CL F,CL... A>auto freq(F&&f,A&&...a)->DCLT(Rg invoke(FWD(f),FWD(a)...));
#endif
};
TP<CL F,CL... A>concept invocable=CpRef(invocable,F,A...);
#define same_as is_same_v
TP<CL T,CL U>concept same=same_as<rmv_cvr_t<T>,rmv_cvr_t<U>>;
#define def_call(Na,FL) TP<CL...A>auto COP()(A&&...a) FL NOEXP_DCLT_RET(call((Na FL)*this,FWD(a)...))
#define def_sub(Na,FL) TP<CL A>auto COP[](A&&a) FL NOEXP_DCLT_RET(sub((Na FL)*this,FWD(a)))
#define def_all(S,Na) def_##S(Na,&)def_##S(Na,&&)def_##S(Na,const&)def_##S(Na,const&&)
ST deleted_t{};
TP<CL...>CL first_of{};TP<CL...F>first_of(F...) ->first_of<F...>;
TP<CL F,CL...T>CL first_of<F,T...>{
using R=first_of<T...>;
NUA F f;NUA R r;
TP<CL S,CL...A,BL W=invocable<like_t<F,S&&>,A...>,CL X=like_t<conditional_t<W,F,R>,S&&>>
SAC call(S&&s,A&&...a)noexcept(is_nothrow_invocable_v<X,A...>)->inv_res_t<X,A...>
{if CEXP(W)RET(Rg invoke(FWD(s).f,FWD(a)...))else RET(Rg invoke(FWD(s).r,FWD(a)...))}
TpReq(CL S,CL...A)(invocable<like_t<F,S&&>,A...>&&same_as<inv_res_t<like_t<F,S&&>,A...>,deleted_t>)VC call(S&&s,A&&...)=delete;
public:first_of()=default;CEXP first_of(F f,T...t):f(move(f)),r(move(t)...){}
def_all(call,first_of)
};
#define Bind(Na,...) TP<CL F,CL...T>ST Na{TpReq(CL X,CL...Y)(!same<Na,X>)Na(X&&x,Y&&...y):f(FWD(x)),a(FWD(y)...){}\
TP<CL S,CL...X,CL FF=F>SAC call(S&&s,X&&...x)noexcept(is_nothrow_invocable_v<like_t<FF,S&&>,X...,T...>)\
->inv_res_t<like_t<FF,S&&>,X...,T...>RET(apply([&](auto&&...a)RET(Rg invoke(FWD(s).f,__VA_ARGS__)),FWD(s).a))def_all(call,Na)\
private:F f;tuple<T...>a;};TP<CL F,CL...A>Na(F,A...)->Na<F,A...>;
Bind(bindF,FWD(a)...,FWD(x)...)Bind(bindB,FWD(x)...,FWD(a)...)
#undef Bind
TP<CL L,CL R>ST compose{
TP<CL X,CL Y>compose(X&&l,Y&&r):l(FWD(l)),r(FWD(r)){}
TP<CL S,CL...A>SAC call(S&&s,A&&...a)NOEXP_DCLT_RET(Rg invoke(FWD(s).r,Rg invoke(FWD(s).l,FWD(a)...)))def_all(call,compose)
private:L l;R r;};
TP<CL L,CL R>compose(L,R)->compose<L,R>;
TP<CL F>ST raco{using Raco=raco;TP<CL>friend ST raco;raco()=default;TpReq(CL X)(!same<X,raco>)CEXP raco(X&&x):f(FWD(x)){}
SAC __pip__=first_of([](auto&&l,auto&&r)NOEXP_DCLT_RET(Rg invoke(FWD(r),FWD(l))),[](auto&&l,auto&&r)NOEXP_DCLT_RET(compose(FWD(l),FWD(r))));
TpReq(CL L,CL R)(ReqType(TypeInner(Raco,L),TypeInner(Raco,R)))SAC pip(L&&l,R&&r)NOEXP_DCLT_RET(MakeAuto(raco,__pip__(FWD(l).f,FWD(r).f)))
SAC test=[](auto&&r,auto&&...a)NOEXP_DCLT_RET(Rg invoke(FWD(r).f,FWD(a)...));
SAC call=first_of([](auto&&r,auto&&...a)NOEXP_DCLT_RET(Rg invoke(FWD(r).f,FWD(a)...)),
[](auto&&r,auto&&...a)NOEXP_DCLT_RET(MakeAuto(raco,bindB(FWD(r).f,FWD(a)...))));
SAC sub=[](auto&&r,auto&&i)NOEXP_DCLT_RET(MakeAuto(raco,bindF(FWD(r).f,FWD(i))));
def_all(sub,raco)def_all(call,raco)
private:F f;};
TP<CL X>raco(X)->raco<X>;
CpDef(is_raco,CL T)(TY T::Raco)();TP<CL T>concept is_raco=CpRef(is_raco,T);
CPO pipeline=first_of(
    [](auto&&l,auto&&r)DCLT_RET(l.pip(FWD(l),FWD(r))),
    [](auto&&l,auto&&r)DCLT_RET(Rg invoke(FWD(r),FWD(l)))
);
TP<CL L,CL R>auto COP|(L&&l,R&&r)NOEXP_DCLT_RET(pipeline(FWD(l),FWD(r)))
TP<CL L,CL R>auto COP|=(L&&l,R&&r)NOEXP_DCLT_RET(l=pipeline(FWD(l),FWD(r)))
TP<CL L,CL R>auto COP<(L&&l,R&&r)NOEXP_DCLT_RET(Rg invoke(FWD(l),FWD(r)))
TP<CL L,CL R>auto COP<<(L&&l,R&&r)NOEXP_DCLT_RET(FWD(l)[FWD(r)])
TP<CL L,CL R>auto COP%(L&&l,R&&r)NOEXP_DCLT_RET(Rg invoke(FWD(l),FWD(r)))
TP<CL T>decay_t<T>CEXP decay_copy(T&&t)NOEXP(DCLV(decay_t<T>&)=FWD(t))RET(FWD(t))
IC raco Auto=[](auto&&x)NOEXP_DCLT_RET(decay_copy(FWD(x)));
IC raco Move=[](auto&&x)NOEXP_DCLT_RET(move(FWD(x)));//[todo.fix.lvalue]
//[concepts]
CpDef(derived_from,CL D,CL B)()(Reqs(is_convertible_v<const volatile D*,const volatile B*>));
TP<CL D,CL B>concept derived_from=is_base_of_v<B,D>&&CpRef(derived_from,D,B);
//[concept.convertible]
CpDef(conv_to,CL From,CL To)(add_rvalue_reference_t<From>(&f)())(static_cast<To>(f()),);
TP<CL From,CL To>concept conv_to=is_convertible_v<From,To>&&CpRef(conv_to,From,To);
CpDef(com_ref_with,CL T,CL U)()(
Reqs(same_as<com_ref_t<T,U>,com_ref_t<U,T>>)
Reqs(conv_to<T,com_ref_t<T,U>>)
Reqs(conv_to<U,com_ref_t<T,U>>)
);
TP<CL T,CL U>concept com_ref_with=CpRef(com_ref_with,T,U);
CpDef(common_with,CL T,CL U)()(
Reqs(same_as<common_type_t<T,U>,common_type_t<U,T>>)
static_cast<common_type_t<T,U>>(DCLV(T)),
static_cast<common_type_t<T,U>>(DCLV(U)),
Reqs(com_ref_with<add_lvalue_reference_t<const T>,add_lvalue_reference_t<const U>>)
Reqs(com_ref_with<add_lvalue_reference_t<common_type_t<T,U>>,
com_ref_t<add_lvalue_reference_t<const T>,add_lvalue_reference_t<const U>>>)
);
TP<CL T,CL U>concept common_with=CpRef(common_with,T,U);
//[concept.arithmetic]
TP<CL T>concept integral=is_integral_v<T>;
TP<CL T>concept signed_integral=integral<T>&&is_signed_v<T>;
TP<CL T>concept unsigned_integral=integral<T>&&!signed_integral<T>;
TP<CL T>concept floating_point=is_floating_point_v<T>;
CpDef(assignable_from,CL L,CL R)(L l,R&&r)(
RetReq(same_as,L)(l=FWD(r))
Reqs(com_ref_with<const rmv_r_t<L>&,const rmv_r_t<R>&>)
);
TP<CL L,CL R>concept assignable_from=is_lvalue_reference_v<L>&&CpRef(assignable_from,L,R);
TP<CL T>concept destructible=is_nothrow_destructible_v<T>;
TP<CL T,CL... A>concept cst_from=destructible<T>&&is_constructible_v<T,A...>;
CpDef(df_init,CL T)() (T{},::new (static_cast<void*>(nullptr)) T,);
TP<CL T>concept df_init=cst_from<T>&&CpRef(df_init,T);
TP<CL T>concept move_cst=cst_from<T,T>&&conv_to<T,T>;
CpDef(copy_cst,CL T)()(
Reqs(move_cst<T>&&cst_from<T,T&>&&conv_to<T&,T>&&cst_from<T,const T&>)
Reqs(conv_to<const T&,T>&&cst_from<T,const T>&&conv_to<const T,T>)
);
TP<CL T>concept copy_cst=CpRef(copy_cst,T);
//[range.swap]
ST swap_fn{
TP<CL T>static void swap(T&,T&)=delete;TP<CL T,size_t N>static void swap(T(&)[N],T(&)[N])=delete;
TP<CL T,CL U>CEXP static auto impl(T&&t,U&&u,tag<2>)NOEXP_DCLT_RET((void)swap(FWD(t),FWD(u)))
TP<CL T,CL U,size_t N,CL F=swap_fn>CEXP static auto impl(T(&t)[N],U(&u)[N],tag<1>)
NOEXP_DCLT(DCLV(F&)(*t,*u)){for(size_t i=0;i<N;++i)impl(t[i],u[i],tag<2>{});}
TP<CL T>CEXP static auto impl(T& a,T& b,tag<0>)noexcept(is_nothrow_move_constructible_v<T>&&is_nothrow_assignable_v<T&,T>)
->Req(move_cst<T>&&assignable_from<T&,T>,void) {T temp=move(a);a=move(b);b=move(temp);}
TP<CL T,CL U>auto COP()(T&&t,U&&u)const NOEXP_DCLT_RET(swap_fn::impl(FWD(t),FWD(u),tag<2>{}))
};
In_Rgs(In_cpo(raco swap=swap_fn{};))
CpDef(swappable,CL T)(T&a,T&b)(Rg swap(a,b),);
TP<CL T>concept swappable=CpRef(swappable,T);
CpDef(swappable_with,CL T,CL U)(T&&t,U&&u) (
Reqs(com_ref_with<T,U>)
Rg swap(FWD(t),FWD(t)),Rg swap(FWD(u),FWD(u)),Rg swap(FWD(t),FWD(u)),Rg swap(FWD(u),FWD(t)),
);
TP<CL T>concept bool_ts_impl=conv_to<T,bool>;
CpDef(bool_ts,CL T) (T&&t)(Cret(bool_ts_impl,!FWD(t))());
TP<CL T>concept boolean_testable=bool_ts_impl<T>&&CpRef(bool_ts,T);
#define BLT(...) Cret(boolean_testable,__VA_ARGS__)()
CpDef(weakly_eq_cmp_with,CL T,CL U)(const rmv_r_t<T>&t,const rmv_r_t<U>&u)
(BLT(t==u)BLT(t!=u)BLT(u==t)BLT(u!=t));
TP<CL T,CL U>concept weakly_eq_cmp_with=CpRef(weakly_eq_cmp_with,T,U);
TP<CL T>concept eq_cmp=weakly_eq_cmp_with<T,T>;
CpBl(eq_cmp_with,CL T,CL U)(eq_cmp<T>&&eq_cmp<U>&&weakly_eq_cmp_with<T,U>&&
com_ref_with<const rmv_r_t<T>&,const rmv_r_t<U>&>&&eq_cmp<com_ref_t<const rmv_r_t<T>&,const rmv_r_t<U>&>>);
TP<CL T,CL U>concept eq_cmp_with=CpRef(eq_cmp_with,T,U);
CpDef(par_ord_with,CL T,CL U)(const rmv_r_t<T>& t,const rmv_r_t<U>& u)
(BLT(t>u)BLT(t<u)BLT(t<=u)BLT(t>=u)BLT(u<t)BLT(u>t)BLT(u<=t)BLT(u>=t));
TP<CL T,CL U>concept par_ord_with=CpRef(par_ord_with,T,U);
TP<CL T>concept tot_ord=eq_cmp<T>&&par_ord_with<T,T>;
CpDef(tot_ord_with,CL T,CL U)()(
Reqs(tot_ord<T>&&tot_ord<U>&&eq_cmp_with<T,U>&&par_ord_with<T,U>)
Reqs(tot_ord<com_ref_t<const rmv_r_t<T>&,const rmv_r_t<U>&>>)
);
TP<CL T,CL U>concept tot_ord_with=CpRef(tot_ord_with,T,U);
//[concept.movable]
CpDef(movable,CL T)()(Reqs(is_object_v<T>&&move_cst<T>&&assignable_from<T&,T>&&swappable<T>));
TP<CL T>concept movable=CpRef(movable,T);
//[concept.copyable]
CpDef(copyable,CL T)()(
Reqs(copy_cst<T>&&movable<T>)
Reqs(assignable_from<T&,T&>&&assignable_from<T&,const T&>&&assignable_from<T&,const T>)
);
TP<CL T>concept copyable=CpRef(copyable,T);
//[concept.semiregular]
TP<CL T>concept semiregular=copyable<T>&&df_init<T>;
//[concept.regular]
TP<CL T>concept regular=semiregular<T>&&eq_cmp<T>;
//[concept.predicate]
CpBl(predicate,CL F,CL...A)(invocable<F,A...>&&boolean_testable<inv_res_t<F,A...>>);
TP<CL F,CL... A>concept predicate=CpRef(predicate,F,A...);
TP<CL R,CL T,CL U>concept relation=predicate<R,T,T>&&predicate<R,U,U>&&predicate<R,T,U>&&predicate<R,U,T>;
CpDef(tplk, CL T)()(RetReq(same_as,size_t)(tuple_size_v<T>));//[todo]more
TP<CL T>concept tuple_like=CpRef(tplk,T);
//[traits]
TP<CL T>using idx_tp=make_index_sequence<tuple_size_v<rmv_cvr_t<T>>>;

TP<CL F>ST Yc_{
F f;
TP<CL...A>auto COP()(A&&...a)const NOEXP_DCLT_RET(f(*this,(A&&)a...))
};
TP<CL F> ST Yc:raco<Yc_<F>>{
    using B=raco<Yc_<F>>;
    TP<CL L>Yc(L&&l):B(Yc_<F>{FWD(l)}){}
};
TP<CL T>Yc(T)->Yc<T>;
TP<CL F>ST scope_guard{F f;TP<CL L>scope_guard(L&&f):f(FWD(f)){}~scope_guard(){f();}};TP<CL F>scope_guard(F)->scope_guard<F>;

//[int]
TP<CL T>CEXP make_unsigned_t<T>to_unsigned(T t)noexcept RET(t)
TP<CL T>CEXP make_signed_t<T>to_signed(T t)noexcept RET(t)
#define Ta [](auto a)noexcept->Req(integral<DCLT(a)>)
#define gN auto x=to_unsigned(a);using T=DCLT(x);AC N=digits_<T>();
TP<CL T>AC digits_(){auto x=limits<T>::digits;RET(x?x:128)};
raco countl_zero=Ta{gN
if(x==0)RET(N)
if CEXP(N<=32)RET(__builtin_clz(x))else if CEXP(N<=64)RET(__builtin_clzl(x))
else {if(ull h=x>>64;h)RET(__builtin_clzl(h)-(2*64-N))RET((N-32)+__builtin_clzl(x&(ull{}-1)))}
};
raco countr_zero=Ta{gN
if(!x)RET(N);
if CEXP(N<=32)RET(__builtin_ctz(x))else if CEXP(N<=64)RET(__builtin_ctzl(x))
else{if (ull l=x&(ull{}-1);l)RET(__builtin_ctzll(l))RET(__builtin_ctzll(ull(x>>64))+64)}
};
raco popcount=Ta{gN
if(!x)RET(0)
if CEXP(N<=32)RET(__builtin_popcount(x))else if CEXP(N<=64)RET(__builtin_popcountl(x))
else RET(__builtin_popcountll(ull(x&limits<ull>::max()))+__builtin_popcountll(ull(x>>64)))
};
raco bit_ceil=Ta{gN
if(!x||x==1)RET(1)
RET((T)1u << (N-countl_zero((T)(x-1u))))
};
raco bit_floor=Ta{gN
if(!x)RET(0)
RET((T)1u<<(N-countl_zero((T)(x>>1))))
};
raco bit_width=Ta{gN
RET(N-countl_zero(x))
};
TpReq(CL T,CL F)(sizeof(T)==sizeof(F))auto bit_cast(const F&s)noexcept{T d;memcpy(&d,&s,sizeof(T));RET(d)}
NP ranges{
using std::empty,std::data;
inline NP cpo {
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
TP<CL X,CL Y>proj_cmp(X&&x,Y&&y):c((X&&)x),p((Y&&)y) {}
TP<CL T,CL U>BL COP()(T&&t,U&&u)const RET(Rg invoke(c,Rg invoke(p,(T&&)t),Rg invoke(p,(U&&)u)))
C c;P p;
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
ST ct_i_tag:ra_i_tag {};
//[incrementable.traits]
TP<CL T>ST incrementable_traits;
TP<CL,CL=Req(1)>ST inti{};
TP<CL T>ST cond_d{using difference_type=T;};
TP<>ST inti<void*>{};
TP<CL T>ST inti<T*>:cond_d<ptrdiff_t>{};
TP<CL I>ST inti<const I>:incrementable_traits<I>{};
CpDef(has_diff,CL T)(TY T::difference_type)();
TP<CL T>ST inti<T,Req(CpRef(has_diff,T))>:cond_d<TY T::difference_type>{};
CpDef(can_diff,CL T)(const T&a,const T&b)(RetReq0(integral)(a-b));
TP<CL T>ST inti<T,Req(!is_pointer_v<T>&&!CpRef(has_diff,T) &&CpRef(can_diff,T))>
:cond_d<make_signed_t<DCLT(DCLV(T)-DCLV(T))>>{};
TP<CL T>ST incrementable_traits:inti<T>{};
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
TP<CL T>using ir_t=DCLT(*DCLV(T&));
TP<CL T>using irr_t=DCLT(Rg iter_move(DCLV(T&)));
//[iter.concept]
TP<CL,CL=void>IC BL has_iter_tag=0;
TP<CL T>IC BL has_iter_tag<T,void_t<TY iterator_traits<T>::iterator_category>> =1;
TP<CL,CL=void>IC BL has_iter_concept=0;
TP<CL T>IC BL has_iter_concept<T,void_t<TY T::iterator_concept>> =1;
TP<CL T>AC iter_concept_impl() {
if CEXP(is_pointer_v<T>) return ct_i_tag {};
else if CEXP(has_iter_concept<T>) return TY T::iterator_concept {};
else if CEXP(has_iter_tag<T>) 
return TY iterator_traits<T>::iterator_category {};
}
TP<CL T>using iter_concept=DCLT(iter_concept_impl<T>());
CpDef(can_reference,CL I)(I&)();
TP<CL I>concept can_reference=CpRef(can_reference,I);
//[iterator.concept]
CpDef(ind_read,CL I,CL V=iv_t<I>,CL R=ir_t<I>,CL RR=irr_t<I>)(const I i)(
Cret(same_as,*i)(R)Cret(same_as,Rg iter_move(i))(RR)
Creq(com_ref_with<R&&,V&>)Creq(com_ref_with<R&&,RR&&>)Creq(com_ref_with<RR&&,const V&>)
);
TP<CL I>concept ind_rd=CpRef(ind_read,rmv_cvr_t<I>);
CpDef(ind_wri,CL O,CL T)(O&&o,T&&t)(*o=FWD(t),*FWD(o)=FWD(t),);
TP<CL I>using ic_t=com_ref_t<ir_t<I>,iv_t<I>&>;
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
Creq(can_reference<DCLT(*i)>)
);
TP<CL I>concept io_i=winc<I>&&CpRef(io_i,I);
//[iterator.concept.sentinel] [[todo]]
TP<CL S,CL I>concept s_for=semiregular<S>&&io_i<I>&&weakly_eq_cmp_with<S,I>;
//[iterator.concept.sizedsentinel]
CpDef(sized_s_for,CL S,CL I)(const I&i,const S&s)(
Cret(same_as,s-i)(id_t<I>)
Cret(same_as,i-s)(id_t<I>)
);
TP<CL S,CL I>concept sized_s_for=s_for<S,I>&&CpRef(sized_s_for,S,I);
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
Creq(com_ref_with<inv_res_t<F&,V>,inv_res_t<F&,R>>)
);
TP<CL F,CL I>concept ind_ui=ind_rd<I>&&copy_cst<F>&&CpRef(ind_ui,F,I);
CpDef(ind_bp,CL F,CL I,CL J,CL VI=iv_t<I>&,CL VJ=iv_t<J>&,CL RI=ir_t<I>,CL RJ=ir_t<J>)()(
Creq(predicate<F&,VI,VJ>&&predicate<F&,VI,RJ>&&predicate<F&,RI,VJ>&&predicate<F&,RI,RJ>)
Creq(predicate<F&,ic_t<I>,ic_t<J>>)
);
TP<CL F,CL I,CL J=I>concept ind_bp=ind_rd<I>&&ind_rd<J>&&copy_cst<F>&&CpRef(ind_bp,F,I,J);
TP<CL F,CL...I>using ind_res_t=inv_res_t<F,ir_t<I>...>;
TP<CL,CL,CL=int>ST projected{};
TP<CL I,CL P>ST projected<I,P,Req(ind_rd<I>&&ind_ui<P,I>)>:cond_v<rmv_cvr_t<ind_res_t<P&,I>>>{ind_res_t<P&,I>operator*()const;};
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
TpReq(CL I)(io_i<I>)void COP()(I&i,id_t<I>n)const{if CEXP(ra_i<I>)i+=n;else{if(n>=0)while (n--)++i;else if CEXP(bd_i<I>)while(n++)--i;}}
TpReq(CL I,CL S)(s_for<S,I>)void COP()(I&i,S s)const
{if CEXP(assignable_from<I&,S>) i=move(s);else if CEXP(sized_s_for<S,I>)(*this)(i,s-i);else while(i!=s)++i;}
TpReq(CL I,CL S)(s_for<S,I>)void COP()(I&i,id_t<I> n,S s)const{
    if CEXP(sized_s_for<S,I>){if(abs(n)>=abs(s-i))(*this)(i,s);else(*this)(i,n);}
    else{if(n<0){if CEXP(bd_i<I>)while(n++&&i!=s)--i;}else while(n--&&i!=s)++i;}
}
} advance;
IC ST next_fn {
TpReq(CL I)(io_i<I>) I COP()(I x)const RET(++x)
TP<CL I,CL...A>auto COP()(I x,A...a)const NOEXP_DCLT_RET((advance(x,a...),x)%Auto)
}next;
IC ST prev_fn {
TpReq(CL I)(bd_i<I>)I COP()(I x) const RET(--x)
TpReq(CL I,CL...A)(bd_i<I>)auto COP()(I x,A...a)const NOEXP_DCLT_RET((advance(x,a...),-x)%Auto)
}prev;

//[ranges.range] concepts
CpDef(range,CL T)(T& t)(Rg begin(t),Rg end(t),);
TP<CL T>concept range=CpRef(range,T);
TP<CL>IC BL enable_borrowed_rg=0;
TP<CL T>concept borrowed_rg=range<T>&&(is_lvalue_reference_v<T>|| enable_borrowed_rg<rmv_cvr_t<T>>);
TP<CL T>using i_t=DCLT(Rg begin(DCLV(T&)));
TP<CL T>using s_t=DCLT(Rg end(DCLV(T&)));
TP<CL R>using rs_t=DCLT(Rg size(DCLV(R&)));
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
//[compare]
using less=raco<::less<>>;
//[range.copy]
ST copy_fn {
TP<CL I,CL S,CL O,CL P>
static O CEXP impl(I f,S l,O o,P p) { for (;f!=l; ++f,++o)*o=invoke(p,*f); return o; }
TP<CL R,CL O,CL P=identity>
O COP ()(R&&r,O o,P p={}) const { return impl(begin(r),end(r),move(o),ref(p)); }
};
IC copy_fn copy;
ST min_fn{
TP<CL I,CL S,CL C,CL P>SAC impl(I f,S l,C c,P p){iv_t<I>r=*f;proj_cmp w={c,p};while(++f!=l)if(w(*f,r))r=*f;return r;}
TpReq(CL R,CL C=less,CL P=identity)(range<R>)auto COP()(R&&r,C c={},P p={})const RET(impl(begin(r),end(r),move(c),ref(p)))
TP<CL T,CL C=less,CL P=identity>auto COP()(initializer_list<T>r,C c={},P p={})const RET(impl(begin(r),end(r),move(c),ref(p)))
TP<CL T,CL U,CL C=less,CL P=identity>auto COP()(T&&t,U&&u,C c={},P p={})const
NOEXP_DCLT_RET((proj_cmp(ref(c),ref(p)))(t,u)?com_ref_t<T&&,U&&>(FWD(t)):com_ref_t<T&&,U&&>(FWD(u)))
};
IC raco min=min_fn{};
auto abs=[](auto x)RET(::abs(x));
IC ST sort_fn{
TP<CL I,CL S,CL C,CL P>
static CEXP I impl(I f,S l,C c,P p){auto r=Rg next(f,l);::sort(f,r,proj_cmp(ref(c),ref(p)));return r;}
TpReq(CL R,CL C=less,CL P=identity)(ra_rg<R>)//todo sortable
DCLT(auto) COP()(R&&r,C c={},P p={})const RET(impl(Rg begin(r),Rg end(r),ref(c),ref(p)))
} sort;
IC ST fold_fn {//[[todo]]requirs
TP<CL I,CL S,CL T,CL Op,CL P>static AC impl(I f,S l,T t,Op op,P p) {
using U=rmv_cvr_t<inv_res_t<Op&,T,ind_res_t<P&,I>>>;
if(f==l)RET(U(move(t)))U a=invoke(op,move(t),*f);while(++f!=l)a=invoke(op,move(a),invoke(p,*f));return a;
}
TpReq(CL I,CL S,CL T,CL Op=plus<>,CL P=identity)(ip_i<I>&&s_for<S,I>)
auto COP()(I f,S l,T t,Op op={},P p={}) const RET(impl(move(f),move(l),move(t),ref(op),ref(p)))
TpReq(CL R,CL T,CL Op=plus<>,CL P=identity)(ip_rg<R>)auto COP()(R&&r,T t,Op op={},P p={})const RET(impl(Rg begin(r),Rg end(r),move(t),ref(op),ref(p)))
TP<CL T,CL Op,CL P>ST fn{T t;Op op;P p;
TpReq(CL I,CL S)(ip_i<I>&&s_for<S,I>)auto COP()(I f,S l)RET(impl(move(f),move(l),move(t),ref(op),ref(p)))//[need?]
TpReq(CL R)(ip_rg<R>)auto COP()(R&&r)RET(impl(begin(r),end(r),move(t),ref(op),ref(p)))
TpReq(CL R)(ip_rg<R>)auto FCOP|(R&&r,fn f)RET(impl(begin(r),end(r),move(f.t),ref(f.op),ref(f.p)))
};
TP<CL T,CL Op=plus<>,CL P=identity>auto COP()(T t,Op op={},P p={})const RET(fn<T,Op,P>{move(t),move(op),move(p)})
} fold;

//[interfaces]
TP<CL D>CL view_interface {
CEXP D& derived() noexcept RET(static_cast<D&>(*this))
CEXP const D& derived() const noexcept RET(static_cast<const D&>(*this))
public:using __interface=view_interface;
LazyT(D,fw_rg<t>) CEXP BL empty() RET(begin(derived())==end(derived()))
LazyT(D,fw_rg<const t>) CEXP BL empty() const RET(begin(derived())==end(derived()))
LazyT(D,ReqExpr(Rg empty(DCLV(t&)))) explicit COP bool() RET(!Rg empty(derived()) )
LazyT(D,ReqExpr(Rg empty(DCLV(t&)))) explicit COP bool() const RET(!Rg empty(derived()) )
LazyT(D,ReqExpr(range<D>&&ct_i<i_t<t>>)) AC data()
->DCLT(&*Rg begin(DCLV(t&)))RET(&*begin(derived()))
LazyT(D,ReqExpr(range<const D>&&ct_i<i_t<const t>>)) AC data()
const->DCLT(&*Rg begin(DCLV(const t&))) RET(&*begin(derived()))
LazyT(D,fw_rg<t>&&sized_s_for<s_t<t>,i_t<t>>)
AC size() RET(Rg end(derived())-Rg begin(derived()))
LazyT(D,fw_rg<const t>&&sized_s_for<s_t<const t>,i_t<const t>>)
AC size() const RET(end(derived())-::begin(derived()))
LazyT(D,fw_rg<t>) CEXP DCLT(auto) front() RET(*begin(derived()))
LazyT(D,fw_rg<const t>) CEXP DCLT(auto) front() const RET(*begin(derived()))
LazyT(D,bd_rg<t>&&cm_rg<t>) CEXP DCLT(auto) back() RET(*prev(end(derived())))
LazyT(D,bd_rg<const t>&&cm_rg<const t>) CEXP DCLT(auto) back() const RET(*prev(end(derived())))
LazyT(D,ra_rg<t>) DCLT(auto) COP[](rd_t<t>n) RET(begin(derived())[n])
LazyT(D,ra_rg<t>) DCLT(auto) COP[](rd_t<t>n) const RET(begin(derived())[n])
};
TP<CL I,CL Tg,CL D,CL V, CL Ref>CL IF{//Need:adv inc dec,friend:dif lt eq:lt:df_t
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
//[range.utility]
TP<CL V>concept simple_view=view<V>&&range<const V>&&same_as<i_t<V>,i_t<const V>>&&same_as<s_t<V>,s_t<const V>>;
CpDef(has_arrow,CL I)(I i)(i.operator->(),);
TP<CL I>concept has_arrow=ip_i<I>&&(is_pointer_v<I>|| CpRef(has_arrow,I));
TP<CL T,CL U>concept different_from=!same_as<rmv_cvr_t<T>,rmv_cvr_t<U>>;
ST dangling { dangling()noexcept=default;TP<CL...A>dangling(A&&...){} };
TP<CL T>ST box_:optional<T>{
using optional<T>::optional;
LazyT(T,!df_init<T>) box_()=delete;
LazyT(T,df_init<T>)CEXP box_()noexcept(is_nothrow_default_constructible_v<T>):optional<T>{in_place}{}
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
//[range.subrange]
enum CL subrange_kind {sized,unsized};
TP<CL From,CL To>concept conv_to_non_slicing=
conv_to<From,To>&&!(is_pointer_v<decay_t<From>>&&is_pointer_v<decay_t<To>>&&
different_from<remove_pointer_t<decay_t<From>>,remove_pointer_t<decay_t<To>>>);
TP<CL I,CL S=I,subrange_kind K= sized_s_for<S,I>? subrange_kind::sized:subrange_kind::unsized>
CL subrange:public view_interface<subrange<I,S,K>>{
static_assert(io_i<I>);
static_assert(s_for<S,I>);
static_assert(K==subrange_kind::sized || !sized_s_for<S,I>);
static CEXP BL StoreSize=(K==subrange_kind::sized &&!sized_s_for<S,I>);
using sz_t=make_unsigned_t<id_t<I>>;
public:subrange()=default;
TpReq(CL II)(conv_to_non_slicing<II,I>&&!StoreSize)CEXP subrange(II i,S s):i(move(i)),s{s}{}
TpReq(CL II)(conv_to_non_slicing<II,I>&&K==subrange_kind::sized)CEXP subrange(II i,S s,sz_t n):i(move(i)),s{s},sz{n}{}
TpReq(CL R)(borrowed_rg<R>&&conv_to_non_slicing<i_t<R>,I>&&conv_to<s_t<R>,S>&&StoreSize)
CEXP subrange(R&&r):subrange(r,Rg size(r)){}
TpReq(CL R)(borrowed_rg<R>&&conv_to_non_slicing<i_t<R>,I>&&conv_to<s_t<R>,S>&&!StoreSize)
subrange(R&&r):subrange(Rg begin(r),Rg end(r)) {}
TpReq(CL R)(borrowed_rg<R>&&conv_to_non_slicing<i_t<R>,I>&&conv_to<s_t<R>,S>&&K==subrange_kind::sized)
CEXP subrange(R&&r,sz_t n):subrange(Rg begin(r),Rg end(r),n) {}
LazyT(I,copyable<I>)AC begin()const RET(i)
LazyT(I,!copyable<I>)AC begin()RET(move(i))
CEXP S end()const RET(s)
CEXP BL empty()const RET(i==s)
LazyV(K,K==subrange_kind::sized)CEXP sz_t size()const{if CEXP(StoreSize)return sz; else return to_unsigned(s-i);}
private:I i; S s; NUA conditional_t<StoreSize,sz_t,dangling>sz;
};

TpReq(CL I,CL S)(s_for<S,I>)subrange(I,S)->subrange<I,S>;
TpReq(CL I,CL S)(s_for<S,I>)subrange(I,S,make_unsigned_t<id_t<I>>)->subrange<I,S,subrange_kind::sized>;
TpReq(CL R)(borrowed_rg<R>)subrange(R&&)->subrange<i_t<R>,s_t<R>,
(sz_rg<R>|| sized_s_for<i_t<R>,s_t<R>>) ? subrange_kind::sized:subrange_kind::unsized>;
TpReq(CL R)(borrowed_rg<R>)subrange(R&&,make_signed_t<rd_t<R>>)
->subrange<i_t<R>,s_t<R>,subrange_kind::sized>;
#define Head CL I,CL S,Rg subrange_kind K
#define Name Rg subrange<I,S,K>
#define Body {if CEXP(N==0)RET(r.begin())else RET(r.end())}
TP<size_t N,Head>AC get(const Name&r)Body TP<size_t N,Head>AC get(Name&&r)Body
}//ranges
}//my
TP<Head>ST tuple_size<Name>:integral_constant<size_t,2>{};
TP<Head>ST tuple_element<0,Name>:ty_id<I>{};TP<Head>ST tuple_element<0,const Name>:ty_id<I>{};\
TP<Head>ST tuple_element<1,Name>:ty_id<S>{};TP<Head>ST tuple_element<1,const Name>:ty_id<S>{};\
using my::ranges::get;
#undef Head
#undef Name
#undef Body
inline NP my{
#define Def_Vw_Adp(Name) In_Vws(IC raco Name=[](auto&&...a)NOEXP_DCLT_RET(Name##_view{FWD(a)...});)
#define Def_Vw_Adp_(X,...) In_Vws(IC raco X=__VA_ARGS__;)
NP ranges{
//[single.view]
TpReq(CL T)(is_object_v<T>&&copy_cst<T>)ST single_view:view_interface<single_view<T>>{
TpReq(CL U)(same_as<rmv_cvr_t<U>,T>)CEXP explicit single_view(U&&u):v_(FWD(u)){}
TpReq(CL...A)(cst_from<T,A...>)CEXP explicit single_view(in_place_t l,A&&...a):v_{l,FWD(a)...}{}
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
Def_Vw_Adp(single)
//[iota.view]
CpDef(dec,CL I)(I i)(RetReq(same_as,I&)(--i)RetReq(same_as,I)(i--));
TP<CL T>concept decrementable=incrementable<T>&&CpRef(dec,T);
CpDef(adv,CL I)(I i,const I j,const id_t<I>n)(
RetReq(same_as,I&)(i+=n)
RetReq(same_as,I&)(i-=n)
I(j+n),
I(n+j),
I(j-n),
Cret(conv_to,j-j)(id_t<I>)
);
TP<CL T>concept advanceable=decrementable<T>&&tot_ord<T>&&CpRef(adv,T);
TP<CL W,CL B=unr_t>CL iota_view:public view_interface<iota_view<W,B>>{
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
LazyT(W,1)D FC dif Crefp(I)
{if CEXP(is_integral_v<W>){if CEXP(is_signed_v<W>)RET(D(D(i.v)-D(j.v)))else RET(j.v>i.v?D(-D(j.v-i.v)):D(i.v-j.v))}else RET(i.v-j.v)}
public:I()=default;CEXP explicit I(W v):v(v){}W COP*()const RET(v)
};
ST S:SF<S>{
friend SF<S>;
S()=default;CEXP explicit S(B b):b(b) {}
private:B b;
CEXP BL eq(const I&i)const RET(b==i.v)LazyT(W,sized_s_for<B,W>)CEXP BL dif(const I&i)const RET(b-i.v)
};
W v; B b;
public:
iota_view()=default;
CEXP explicit iota_view(W v):v(v) {}
CEXP iota_view(ty_id_t<W>v,ty_id_t<B>b):v(v),b(b) {}
CEXP I begin() const { return I{v}; }
AC end() const {
if CEXP(is_same_v<W,B>) return I{b};
else if CEXP(is_same_v<B,unr_t>) return unr;
else return S{b};
}
LazyT(W,same_as<W,B>|| (integral<W>&&integral<B>) || sized_s_for<B,W>) AC size() const {
if CEXP(is_integral_v<W>&&is_integral_v<B>)
return v<0 ? b<0 ? to_unsigned(-v)-to_unsigned(-b):to_unsigned(b) + to_unsigned(-v):to_unsigned(b)-to_unsigned(v);
else return to_unsigned(b-v);
}
};
TP<CL W,CL B>iota_view(W,B)->iota_view<W,B>;
Def_Vw_Adp(iota)
TP<BL C,CL T>using maybe_const=conditional_t<C,const T,T>;
//[range.ref.view]
TpReq(CL R)(range<R>&&is_object_v<R>)CL ref_view:public view_interface<ref_view<R>>{
ST ref_req_concept{static void FUN(R&); static void FUN(R&&)=delete;TP<CL T>auto freq()->DCLT(FUN(DCLV(T)));};
R*r;
public:TpReq(CL T)(different_from<T,ref_view>&&conv_to<T,R&>&&CpRef(ref_req,T))
CEXP ref_view(T&&t):r(&(R&)(FWD(t))){}
CEXP R& base()const RET(*r)
AC begin() const RET(Rg begin(*r))
AC end() const RET(Rg end(*r))
LazyT(R,ReqExpr(Rg empty(*DCLV(t)))) CEXP BL empty() const RET(Rg empty(*r))
LazyT(R,sz_rg<R>)AC size() const RET(Rg size(*r))
LazyT(R,ct_rg<R>)AC data() const RET(Rg data(*r))
};
TP<CL R>ref_view(R&)->ref_view<R>;
TP<CL>IC BL init_ls=0;TP<CL T>IC BL init_ls<initializer_list<T>> =1;
TpReq(CL R)(movable<R>&&!init_ls<R>)ST owning_view:view_interface<owning_view<R>>{
owning_view()=default;owning_view(R&&r):r_(move(r)){}
#define Es(Na,F,...) LazyT(R,__VA_ARGS__)AC Na()F RET(Rg Na(r_))
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
Def_Vw_Adp_(all,first_of(
    [](auto&&r)NOEXP_DCLT_RET(Reqs(view<rmv_cvr_t<DCLT(r)>>)decay_copy(FWD(r))),
    [](auto&&r)NOEXP_DCLT_RET(ref_view{FWD(r)}),[](auto&&r)NOEXP_DCLT_RET(owning_view{FWD(r)})
))
In_Vws(TP<CL T>using all_t=DCLT(all(DCLV(T)));)
//[view.transform]
TpReq(CL V,CL F)(ip_rg<V>&&view<V>&&copy_cst<F> &&is_object_v<F>&&
invocable<F&,rr_t<V>>&&can_reference<inv_res_t<F&,rr_t<V>>>) 
CL transform_view:public view_interface<transform_view<V,F>>{
TP<BL>ST S;
#define B maybe_const<C,V>
#define D rd_t<B>
TP<BL C>using Tg=conditional_t<ra_rg<B>,ra_i_tag,conditional_t<bd_rg<B>,bd_i_tag,conditional_t<fw_rg<B>,fw_i_tag,ip_i_tag>>>;
TP<BL C>using T=rmv_cvr_t<inv_res_t<F&,rr_t<B>>>;//maybe_const<C,F>&?[[todo]]
TP<BL C>using R=inv_res_t<F&,rr_t<B>>;
#define Fa IF<I<C>,Tg<C>,D,T<C>,R<C>>
TP<BL C>CL I:public Fa{
friend Fa;TP<BL>friend ST S;TP<BL>friend ST I;
#undef Fa
using P=maybe_const<C,transform_view>;using Ty=i_t<B>;
VC inc(){++i_;}LazyT(B,1)VC dec(){--i_;}LazyT(B,1)VC adv(D n){i_+=n;}
LazyT(B,eq_cmp<Ty>) BL FC eq Crefp(I)RET(i.i_==j.i_)
LazyT(B,1)BL FC lt Crefp(I)RET(i.i_<j.i_)LazyT(B,1)D FC dif Crefp(I) RET(i.i_-j.i_)
Ty i_;P*p_;public:
I()=default;CEXP I(P&p,Ty c):p_(&p),i_(c){}LazyT(V,C&&conv_to<i_t<V>,Ty>)CEXP I(I<!C>i):i_(move(i.i_)),p_(i.p_){}
AC base()const&RET(i_)AC base()&&RET(move(i_))
DCLT(auto) COP*() const RET(Rg invoke(*p_->f_,*i_))
FC DCLT(auto)iter_move(const I&i)NOEXP(Rg invoke(*p_->f_,*i_)){if CEXP(is_lvalue_reference_v<DCLT(*i)>)RET(move(*i))return*i;}
LazyT(B,ind_sw<i_t<B>>)FC auto iter_swap Crefp(I)NOEXP_RET(Rg iter_swap(i.i_,j.i_))
};
TP<BL C>CL S:public SF<S<C>> {
TP<BL>friend ST S;friend SF<S<C>>;
using Pa=maybe_const<C,transform_view>;using Ty=s_t<B>;Ty s_;
#define Def(Na) TpReq(BL CC)(Na##s_for<Ty,i_t<maybe_const<CC,V>>>)
Def()BL eq(const I<CC>&i)const RET(s_==i.i_)Def(sized_)D dif(const I<CC>&i)const RET(s_-i.i_)
#undef D
#undef B
#undef Def
public:AC base()RET(s_)
S()=default;CEXP S(Ty s):s_(move(s)){}LazyT(V,C&&conv_to<s_t<V>,Ty>)CEXP S(S<!C>s):s_(move(s.s_)){}
};
V v_=V();copyable_box<F>f_;
public:
CEXP transform_view(V v,F f):v_(move(v)),f_(move(f)) {}
CEXP V base()const RET(v_)
CEXP I<0>begin() RET({*this,Rg begin(v_)})
LazyT(V,range<const t>&&invocable<const F&,rr_t<const t>>)
CEXP I<1>begin() const RET({*this,::begin(v_)})
AC end() {if CEXP(cm_rg<V>)RET(I<0>{*this,Rg end(v_)})else RET(S<0>{Rg end(v_)})}
LazyT(V,range<const t>&&invocable<const F&,rr_t<const t>>) AC end() const {
if CEXP(cm_rg<V>) return I<1>{*this,::end(v_)};
else return S<1>{::end(v_)};
}
LazyT(V,sz_rg<V>) AC size() RET(::size(v_) )
LazyT(V,sz_rg<const V>)AC size() const RET(::size(v_) )
};
TP<CL R,CL F>transform_view(R&&,F)->transform_view<Vw all_t<R>,F>;
Def_Vw_Adp(transform)
IC ST search_fn {
TP<CL I,CL S,CL J,CL T,CL Pr,CL P,CL Q>subrange<I>static impl(I a,S b,J x,T y,Pr pr,P p,Q q){
for (;;++a) {I i=a;
for(J j=x;;++i,++j){if(j==y)RET({a, i})if(i==b)RET({i,i})if(!invoke(pr,invoke(p,*i),invoke(q,*j)))break;}
}
}
TpReq(CL R,CL S,CL Pr=equal_to<>,CL P=identity,CL Q=identity)(fw_rg<R>&&fw_rg<S>&&ind_cmp<i_t<R>,i_t<S>,Pr,P,Q>)
AC operator()(R&&r,S&&s,Pr pr={},P p={},Q q={})const RET(impl(ALL(r),ALL(s),ref(pr),ref(p),ref(q)))
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
VC inc(){i_=n_.begin();if(i_!=Rg end(p_->v_)){i_=n_.end();if(i_==Rg end(p_->v_)){t_=1;n_={i_,i_};}else n_=p_->Nx(i_);} else t_=0;}
FC BL eq Crefp(I)RET(i.i_==j.i_&&i.t_==j.t_)BC rte()const RET(i_==Rg end(p_->v_)&&!t_)
public:I()=default;CEXP I(split_view&p,VI i,R n):p_(&p),i_(i),n_(n){}VI base()const RET(i_)R COP*()const RET({i_,n_.begin()})
};
#define RV rv_t<R>
public:CEXP split_view(V v,P p):v_(move(v)),p_(move(p)){}CEXP split_view(V v,RV p):v_(move(v)),p_(move(Vw single(p))){}
CEXP I begin()RET({*this,Rg begin(v_),Nx(Rg begin(v_))})
AC end(){if CEXP(cm_rg<V>)RET(I{*this,Rg end(v_),{}})else RET(df)}
};
TP<CL R,CL P>split_view(R&&,P&&)->split_view<Vw all_t<R>, Vw all_t<P>>;
TP<CL R>split_view(R&&,RV)->split_view<Vw all_t<R>, single_view<RV>>;
Def_Vw_Adp(split)
#undef RV
//[range.reverse.view]
TP<CL V>ST reverse_view:view_interface<reverse_view<V>>{
private:
TP<BL X=1>using RI=enable_if_t<X,reverse_iterator<i_t<V>>>;
TP<CL T>using RS=enable_if_t<sz_rg<T>,rd_t<T>>;
public:
CEXP explicit reverse_view(V v):v_(move(v)){}
CEXP V base()const& { return v_; }
TP<CL VV=V>RI<>CEXP begin() { return make_reverse_iterator(Rg next(::begin(v_),::end(v_))); }
TP<CL VV=V>RI<range<const VV>>CEXP begin() const 
{ return make_reverse_iterator(Rg next(::begin(v_),::end(v_))); }
TP<CL VV=V>RI<>CEXP end() { return make_reverse_iterator(::begin(v_)); }
TP<CL VV=V>RI<range<const VV>>CEXP end() const { return make_reverse_iterator(::begin(v_)); }
TP<CL VV=V>RS<VV>CEXP size() { return::size(v_); }
TP<CL VV=V>RS<const VV>CEXP size() const { return::size(v_); }
private:V v_;
};
TP<CL T>reverse_view(T&&)->reverse_view<Vw all_t<T>>;
Def_Vw_Adp(reverse)//first_of [todo]
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
CL drop_while_view:public view_interface<drop_while_view<V,P>>{
V v_;
copyable_box<P>p_;
public:
drop_while_view(V v,P p):v_(move(v)),p_(move(p)){}
AC begin() RET(Rg find_if_not(v_,cref(*p_)))
AC end() RET(Rg end(v_))
LazyT(V,copy_cst<V>) CEXP V base() const& RET(v_)
CEXP V base()&&RET(move(v_))
};
Def_Vw_Adp(drop_while)
//[range.view.zip]
TP<CL...A>using tuple_or_pair=tuple<A...>;
TP<CL... R>concept czip=(sizeof...(R)==1&&(cm_rg<R>&&...))||(!(bd_rg<R>&&...)&&(cm_rg<R>&&...))||((ra_rg<R>&&sz_rg<R>)&&...);
TP<CL F,CL Tp>AC tfe_(F&&f,Tp&&tp) { apply([&](auto&&...a){ (invoke(f,FWD(a)),...); },FWD(tp) ); }
TP<CL F,CL Tp>AC ttf_(F&&f,Tp&&tp) 
RET(apply([&](auto&&...a)RET(tuple_or_pair<inv_res_t<F&,DCLT(a)>...>(invoke(f,FWD(a))...)),FWD(tp)))
TP<CL F,CL L,CL R,size_t... i>AC tpt_impl(F&&f,L&&l,R&&r,index_sequence<i...>)
RET(tuple_or_pair<DCLT(invoke(FWD(f),get<i>(FWD(l)),get<i>(FWD(r))))...>(invoke(FWD(f),get<i>(FWD(l)),get<i>(FWD(r)))...))
TP<CL F,CL L,CL R>AC ttf_(F&&f,L&&l,R&&r)
RET(tpt_impl(FWD(f),FWD(l),FWD(r),make_index_sequence<tuple_size_v<rmv_cvr_t<L>>>{}))
TP<CL F,CL L,CL R,size_t... i>VC tpf_impl(F&&f,L&&l,R&&r,index_sequence<i...>)
RET((invoke(FWD(f),get<i>(FWD(l)),get<i>(FWD(r))),...))
TP<CL F,CL L,CL R>AC tfe_(F&&f,L&&l,R&&r)
RET(tpf_impl(FWD(f),FWD(l),FWD(r),make_index_sequence<tuple_size_v<rmv_cvr_t<L>>>{}))
TP<CL... V>CL zip_view:public view_interface<zip_view<V...>>{
#define MCV maybe_const<C,V>
#define TMCV(Name) tuple_or_pair<Name<MCV>...>
#define All_(...) (__VA_ARGS__##_rg<MCV>&&...)
static_assert(sizeof...(V)>0&&((view<V>&&ip_rg<V>) &&...));
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
CurLazy(C&&(conv_to<i_t<V>,i_t<MCV>>&&...))CEXP I(I<!C>i):i_(move(i.i_)) {}
auto COP*()const RET(ttf_([](auto&i)->DCLT(auto)RET(*i),i_))
void FC iter_move(const I&i)RET(ttf_(Rg iter_move,i.i_))
CurLazy((ind_sw<i_t<MCV>>&&...))void FC iter_swap Crefp(I){tfe_(Rg iter_swap,i.i_,j.i_);}
private:TMCV(i_t)i_;
VC inc(){tfe_([](auto&i){++i;},i_);}CurLazy(1)void dec(){tfe_([](auto& i){--i;},i_);}
CurLazy(1)void adv(D<C>n){tfe_([n](auto&i){i+=n;},i_);}
CurLazy((eq_cmp<i_t<MCV>>&&...))BL FC eq Crefp(I){if CEXP(All_(bd))RET(i.i_==j.i_)else
RET(apply([](auto...b)RET((b||...)),ttf_([](auto&i,auto&j)RET(i==j),i.i_,j.i_)))}
CurLazy(1)BL FC lt Crefp(I)RET(i.i_<j.i_)
CurLazy(1)D<C>FC dif Crefp(I)RET(apply([](auto... b) RET(min({(D<C>)b...},{},abs)),ttf_([](auto&i,auto&j)RET(i-j),i.i_,j.i_)))
#undef All_
};
TP<BL C>ST S:SF<S<C>>{
friend SF<S<C>>;S()=default;S(TMCV(s_t) s_):s_(move(s_)){}
CurLazy(C&&(conv_to<s_t<V>,s_t<MCV>>&&...))CEXP S(S<!C>i):s_(i.s_){}
private:TMCV(s_t)s_;
#define Def(Name) TpReq(BL CC)((Name##s_for<s_t<MCV>,i_t<maybe_const<CC,V>>>&&...))CEXP
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
CurLazy(!(simple_view<V>&&...)) AC end() {
if CEXP(!czip<V...>) return S<0>(ttf_(Rg end,v_));
else if CEXP((ra_rg<V>&&...)) return begin() + size();
else return I<0>(ttf_(Rg end,v_));
}
CurLazy((range<const V>&&...)) AC end()const{
if CEXP(!czip<const V...>) return S<0>(ttf_(Rg end,v_));
else if CEXP((ra_rg<const V>&&...)) return begin() + size();
else return I<0>(ttf_(Rg end,v_));
}
CurLazy((sz_rg<V>&&...)) AC size()
RET(apply([](auto...a)RET(Rg min({(make_unsigned_t<common_type_t<DCLT(a)...>>)a...})),ttf_(Rg size,v_)))
CurLazy((sz_rg<const V>&&...)) AC size() const
RET(apply([](auto...a)RET(Rg min({(make_unsigned_t<common_type_t<DCLT(a)...>>)a...})),ttf_(Rg size,v_)))
#undef CurLazy
};
TP<CL... R>zip_view(R&&...)->zip_view<Vw all_t<R>...>;
Def_Vw_Adp(zip)
Def_Vw_Adp_(enumerate,[](auto&&...r)NOEXP_DCLT_RET(zip(iota(size_t{0}),FWD(r)...)))//[todo]:iota(0-size)
IC ST adjacent_find_fn{
TP<CL I,CL S,CL Pr,CL P>CEXP static I impl(I f,S l,Pr pr,P p){
if(f==l)RET(f)auto w=proj_cmp(ref(pr),ref(p));
for(auto n=next(f);n!=l;++n,++f)if(w(*f,*n))break;return f;
}
TpReq(CL R,CL C=equal_to<>,CL P=identity)(fw_rg<R>&&ind_bp<C,projected<i_t<R>,P>>)
auto COP()(R&&r,C c={},P p={})const RET(impl(ALL(r),ref(c),ref(p)))
TpReq(CL I,CL S,CL C=equal_to<>,CL P=identity)(fw_i<I>&&s_for<S,I>&&ind_bp<C,projected<I,P>>)
auto COP()(I f,S l,C c={},P p={})const RET(impl(move(f),move(l),ref(c),ref(p)))
} adjacent_find;
//[views.chunk_by]
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
AC end(){if CEXP(cm_rg<V>)RET(I{*this,Rg end(v_),Rg end(v_)})else RET(df)}
};
TP<CL R,CL P>chunk_by_view(R&&,P)->chunk_by_view<Vw all_t<R>,P>;

Def_Vw_Adp(chunk_by)
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
public:CEXP subset_view(T t) noexcept:t(t) {}
CEXP I begin()const noexcept RET( { t } )CEXP df_t end()const noexcept RET({})
AC size()const noexcept RET( to_unsigned(T{1})  << __popcount(t) )
};
Def_Vw_Adp(subset)
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
Def_Vw_Adp(decompose)
CpDef(can_reserve,CL C)(C&c,size_t n)(
c.reserve(n),
Cret(same_as,c.max_size())(DCLT(c.size()))
Cret(same_as,c.capacity())(DCLT(c.size()))
);
TP<CL C>concept can_reserve=CpRef(can_reserve,C);
TP<CL R>using proxy_iter=istream_iterator<rv_t<R>>;
TP<TPP C,CL R,CL... A>using Cont=DCLT(C(proxy_iter<R>(),proxy_iter<R>(),DCLV(A)...));
TP<CL C>struct to_{
TP<CL E>ST ins_{
SAC get=first_of(
[](C&c)NOEXP_DCLT_RET(ReqExpr(c.push_back(DCLV(E))),back_inserter(c)),
[](C&c)NOEXP_DCLT_RET(ReqExpr(c.insert(end(c),DCLV(E))),inserter(c,end(c)))
);
};
SAC impl=first_of(
[](auto&&r,auto&&...a)NOEXP_DCLT_RET(C(FWD(r),FWD(a)...)),
[](auto&&r,auto&&...a)NOEXP_DCLT_RET(C(begin(r),end(r),FWD(a)...)),
[](auto&&r,auto&&...a)NOEXP_DCLT(ins_<rr_t<DCLT(r)>>::get(DCLV(C)))
{using R=DCLT(r);auto c=C(FWD(a)...);if CEXP(sz_rg<R>)if CEXP(can_reserve<C>)c.reserve(size(r));Rg copy(r,ins_<rr_t<R>>::get(c));return c;}
);
//[bug?]
SC raco fn=impl;
};
TP<TPP C>ST to_tp{
SC ST Impl{TP<CL R,CL...A>auto COP()(R&&r,A&&...a)NOEXP_DCLT_RET(to_<Cont<C,R,A...>>::impl(FWD(r),FWD(a)...))}impl;
SC raco fn=impl;
};
TP<CL C,CL... A>AC to(A&&...a)DCLT_RET(to_<C>::fn(FWD(a)...))
TP<TPP C,CL... A>AC to(A&&...a)DCLT_RET(to_tp<C>::fn(FWD(a)...))
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
TP<CL S,TPP W,CL T,CL...Re,CL=TY tuple_size<rmv_cvr_t<T>>::type,CL=void_t<TY W<T,Re...>::fmt>>
void impl(S&,W<T,Re...>w,tag<2>);
TP<CL S,CL R,CL=Req(Rg range<R>)>void impl(S&s,R&&r,tag<1>);
TP<CL S,CL T,CL=TY tuple_size<rmv_cvr_t<T>>::type>void impl(S&s,T&&t,tag<0>);
//op
TP<CL Ch,CL Tr,CL T>auto operator<<(basic_ostream<Ch,Tr>&s,T&&t)DCLT_RET(impl(s,t,tag<6>{}),s)
//impl
#define DEF auto d=[&]{if CEXP(has_del<WW>)return w.d;else return default_delim;};auto b=[&]{if CEXP(has_bra<WW>)return w.b;else return default_brac;};
#define MSeq make_index_sequence<tuple_size_v<rmv_cvr_t<T>>>{}
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
#define DEF using T=rmv_cvr_t<TT>;using U=rmv_cvr_t<UU>;
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
sf()=default; TP<CL U>CEXP sf(U&&x):v(FWD(x)) {}
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
using L=DCLT(M);L v;
B()=default;CEXP B(L x):v((x%=M)<0?x+=M:x){}
using X=B&;TP<CL...T>using Q=enable_if_t<(integral<T>&&...),B>;
TpReq(CL I)(integral<I>&&!same_as<int,I>) explicit COP I()const{return I(v);}COP int()const{return int(v);}
X COP+=(B r)RET_THIS(v-=M-r.v;if(v<0)v+=M;)X COP-=(B r)RET_THIS(v-=r.v;if(v<0)v+=M;)
X COP*=(B r)RET_THIS((v*=r.v)%=M;)X COP/=(B r)RET(*this*=r.inv();)
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
UF(size_t n):n(n),comp_cnt(n),fa(n),sz(n,1) {
iota(begin(fa),end(fa),0);
}
auto size() { return n; }
auto count() { return comp_cnt; }
int findset(int x) { return fa[x]==x ? x:fa[x]=findset(fa[x]); }
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
AC pop=[](auto& t) {
using T=decay_t<DCLT(t)>;auto r=move((TY T::value_type&)[&]()->auto&&{if CEXP(CpRef(can_top,T))RET(t.top())else RET(t.front())}());
t.pop();return r;
};
}//utility
inline NP direction {
CEXP int dir [][2]{{0,1},{1,0},{0,-1},{-1,0}};
CEXP int dir8[][2]{ {0,1},{1,0},{0,-1},{-1,0},{1,1},{-1,1},{1,-1},{-1,-1}};
AC valid=[](auto m,auto n)RET([=](size_t x,size_t y)RET(x<m&&y<n));
}
#ifdef __cpp_lib_memory_resource
IC auto set_pmr=[] {
static byte buffer [1 << 30];
static auto pool=pmr::monotonic_buffer_resource { data(buffer),size(buffer) };
set_default_resource(&pool);
return 0;
};
#endif
IC auto set_fast_io=[]{ios::sync_with_stdio(0); cin.tie(0); cout.tie(0); cout << setprecision(12); return 0;};
}//my
TP<CL...A>VC swap(const tuple<A...>&i,const tuple<A...>&j){Rg tfe_(Rg swap,i,j);}
TP<CL>concept is_vv=0;TP<CL T>concept is_vv<vector<T>> =1;
TP<CL T>ST tuple_size<vector<T>>:integral_constant<size_t,vector_size_v>{};
TP<size_t I,CL T>ST tuple_element<I,vector<T>>:enable_if<1,T>{};
TpReq(size_t I,CL T)(is_vv<rmv_cvr_t<T>>)DCLT(auto)get(T&&t)RET(FWD(t)[I])
}//std
inline NP simplify {
NP views=Rg views;using Rg to;using Rg subrange;using Rg fold;
CPO fac=Vw decompose; CPO subset=Vw subset;
CPO range=Vw iota; CPO zip=Vw zip; CPO enu=Vw enumerate; CPO split=Vw split;
CPO rev=Vw reverse; CPO tran=Vw transform;CPO single=Vw single;CPO chunk_by=Vw chunk_by;
CPO Min=Rg min;CPO Size=Rg size;
}//simplify
