#include <bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
#define DEBUG
#define NP namespace
using NP std;
NP std {
#ifdef DEBUG
#define debug(...) cout << #__VA_ARGS__ << "\t" << forward_as_tuple(__VA_ARGS__)/ebra << endl;
#else
#define debug(...)
#endif
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
#define FVC friend VC
#define EC explicit CEXP
#define FAC friend AC
#define SAC static AC
#define COP CEXP operator
#define FCOP friend CEXP operator
#define ECOP explicit CEXP operator
#define CPO CEXP inline auto
#define concept IC BL

#define lst initializer_list
#define NUA [[__no_unique_address__]]

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

#define Reqs(...) Req(__VA_ARGS__){},
#define HRetReq(...) __VA_ARGS__ )>>{},
#define RetReq0(Na) requires_expr< Na<DCLT( HRetReq
#define RetReq(Na,...) requires_expr< Na<__VA_ARGS__,DCLT( HRetReq

#define CpDef(NAME,...) ST NAME##_concept { TP<__VA_ARGS__>auto freq HCpDef0
#define HCpDef0(...) (__VA_ARGS__)->DCLT HCpDef1
#define HCpDef1(...) (__VA_ARGS__  void());}

#define CpBl(NAME,...) ST NAME##_concept { TP<__VA_ARGS__>auto freq()->HCpBl0
#define HCpBl0(...) Req(__VA_ARGS__);}
#define Creq Reqs
#define HCret(...) ,##__VA_ARGS__>>{},
#define Cret1(Na,...) requires_expr<Na<DCLT(__VA_ARGS__)>>{},
#define Cret(Na,...) requires_expr<Na<DCLT(__VA_ARGS__) HCret
#define CpRef(NAME,...) requires_<NAME##_concept,__VA_ARGS__>

#define RET_THIS(...) { __VA_ARGS__ return*this;}
#define Crefp(T)(const T&i,const T&j)
#define TypeInner(In,...) TY rmv_cvr_t<__VA_ARGS__>::In
#define Pack(...) __VA_ARGS__

//[requires_]
TP<CL,CL...>auto _req_impl(...)->false_type;TP<CL R,CL...A,CL=DCLT(&R::TP freq<A...>)>auto _req_impl(int)->true_type;
TP<CL R,CL...A>IC BL requires_=DCLT(_req_impl<R,A...>(0))::value;
TP<BL B,CL...>IC BL boolT=B;TP<BL B,auto...>IC BL boolV=B;
TP<BL E,CL T=int>using requires_expr=enable_if_t<E,T>;
//[traits]
#define rmv_r_t remove_reference_t
#define same_as is_same_v
#define cd_t conditional_t
TP<CL T>concept integral=is_integral_v<T>;
TP<CL T>concept signed_integral=integral<T>&&is_signed_v<T>;
TP<CL T>concept unsigned_integral=integral<T>&&!signed_integral<T>;
TP<CL T>concept floating_point=is_floating_point_v<T>;
TP<CL T>ST ty_id{using type=T;};TP<CL T>using ty_id_t=TY ty_id<T>::type;
TP<CL T>ST remove_cvref:remove_cv<rmv_r_t<T>>{};TP<CL T>using rmv_cvr_t=TY remove_cvref<T>::type;
TP<CL T,CL>ST like:ty_id<T>{};
#define F(FL) TP<CL T,CL U>ST like<T,U FL>:ty_id<T FL>{};
F(&)F(&&)F(const)F(const&)F(const&&)
#undef F
TP<CL T,CL U>using like_t=TY like<rmv_cvr_t<T>,U>::type;
#define limits numeric_limits
using ull=unsigned long long;
using lll=__int128;
using ulll=unsigned __int128;
TP<>ST is_integral<lll>:true_type{};TP<>ST is_integral<ulll>:true_type{};
TP<>ST make_signed<lll>:ty_id<lll>{};TP<>ST make_signed<ulll>:ty_id<lll>{};
TP<>ST make_unsigned<lll>:ty_id<ulll>{};TP<>ST make_unsigned<ulll>:ty_id<ulll>{};
TP<auto M=int64_t(1e9+7)>ST B{using L=DCLT(M);L v;
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

NP pbds_{using NP __gnu_pbds;TP<CL T,CL V=null_type,CL C=less<>>using order_tree=tree<T,V,C,rb_tree_tag,tree_order_statistics_node_update>;}
using pbds_::order_tree;
TP<TPP M,CL...A>auto Hexist(...)->false_type;
TP<TPP M,CL...A,CL=M<A...>>auto Hexist(int)->true_type;
TP<TPP M,CL...A>IC BL Exist=DCLT(Hexist<M,A...>(0))::value;
TP<size_t I>ST tag:tag<I-1>{};TP<>ST tag<0>{};
//[common.reference]
TP<CL...>ST cm_ty;
TP<CL T,CL U>ST copy_cv:ty_id<U>{};
TP<CL T,CL U>ST copy_cv<const T,U>:ty_id<add_const_t<U>>{};
TP<CL T,CL U>ST copy_cv<volatile T,U>:ty_id<add_volatile_t<U>>{};
TP<CL T,CL U>ST copy_cv<const volatile T,U>:ty_id_t<add_cv_t<U>>{};
TP<CL T,CL U>using copy_cv_t=TY copy_cv<T,U>::type;
TP<CL T>using cref_t=add_lvalue_reference_t<const rmv_r_t<T>>;
TP<CL T,CL U>using CondResT=DCLT(1? DCLV(T(&)())():DCLV(U(&)())());
TP<CL A,CL B,CL=rmv_r_t<A>,CL=rmv_r_t<B>,CL=void>ST CmRef{};
TP<CL A,CL B>using CmRefT=TY CmRef<A,B>::type;
TP<CL A,CL B,CL=rmv_r_t<A>,CL=rmv_r_t<B>,CL=void>ST LCmRef{};
TP<CL A,CL B,CL X,CL Y>ST LCmRef<A,B,X,Y,enable_if_t<is_reference_v<CondResT<copy_cv_t<X,Y>&,copy_cv_t<Y,X>&>>>>:ty_id<CondResT<copy_cv_t<X,Y>&,copy_cv_t<Y,X>&>>{};
TP<CL A,CL B>using LCmRefT=TY LCmRef<A,B>::type;
TP<CL A,CL B,CL X,CL Y>ST CmRef<A&,B&,X,Y>:LCmRef<A&,B&>{};
TP<CL X,CL Y>using HrrefCrT=rmv_r_t<LCmRefT<X&,Y&>>&&;
TP<CL A,CL B,CL X,CL Y>ST CmRef<A&&,B&&,X,Y,enable_if_t<
is_convertible_v<A&&,HrrefCrT<X,Y>>&&is_convertible_v<B&&,HrrefCrT<X,Y>>>>:ty_id<HrrefCrT<X,Y>>{};
TP<CL A,CL B,CL X,CL Y>ST CmRef<A&&,B&,X,Y,enable_if_t<is_convertible_v<A&&,LCmRefT<const X&,Y&>>>>:ty_id<LCmRefT<const X&,Y&>>{};
TP<CL A,CL B,CL X,CL Y>ST CmRef<A&,B&&,X,Y>:CmRef<B&&,A&>{};
TP<CL>ST xref { TP<CL U>using type=U;};
TP<CL A>ST xref<A&>{ TP<CL U>using type=add_lvalue_reference_t<TY xref<A>::TP type<U>>;};
TP<CL A>ST xref<A&&>{ TP<CL U>using type=add_rvalue_reference_t<TY xref<A>::TP type<U>>;};
TP<CL A>ST xref<const A>{ TP<CL U>using type=add_const_t<TY xref<A>::TP type<U>>;};
TP<CL A>ST xref<volatile A>{ TP<CL U>using type=add_volatile_t<TY xref<A>::TP type<U>>;};
TP<CL A>ST xref<const volatile A>{ TP<CL U>using type=add_cv_t<TY xref<A>::TP type<U>>;};
TP<CL T,CL U,TP<CL>CL TQual,TP<CL>CL UQual>ST bs_cm_ref{};
TP<CL...>ST cm_ref;
TP<CL... Ts>using cm_ref_t=TY cm_ref<Ts...>::type;
TP<CL T0>ST cm_ref<T0>:ty_id<T0>{};
TP<CL T,CL U>IC BL HCmRefV=Exist<CmRefT,T,U>;
TP<CL T,CL U>using bs_cm_ref_t=TY bs_cm_ref<rmv_cvr_t<T>,rmv_cvr_t<U>,xref<T>::TP type,xref<U>::TP type>::type;
TP<CL T,CL U>IC BL Hbs_cm_ref_v=Exist<bs_cm_ref_t,T,U>;
TP<CL T,CL U>IC BL HCondResV=Exist<CondResT,T,U>;
TP<CL T,CL U,CL=void>ST cmR2:cm_ty<T,U>{};
TP<CL T,CL U>ST cmR2<T,U,enable_if_t<HCmRefV<T,U>>>:CmRef<T,U>{};
TP<CL T,CL U>ST cmR2<T,U,enable_if_t<Hbs_cm_ref_v<T,U>&&!HCmRefV<T,U>>>:ty_id<bs_cm_ref_t<T,U>>{};
TP<CL T,CL U>ST cmR2<T,U,enable_if_t<HCondResV<T,U>&&!Hbs_cm_ref_v<T,U>&&!HCmRefV<T,U>>>:ty_id<CondResT<T,U>>{};
TP<CL T1,CL T2>ST cm_ref<T1,T2>:cmR2<T1,T2>{};
TP<CL,CL,CL,CL...>ST cmR3{};
TP<CL T1,TY T2,CL...R>ST cmR3<void_t<cm_ref_t<T1,T2>>,T1,T2,R...>:cm_ref<cm_ref_t<T1,T2>,R...>{};
TP<CL T1,CL T2,CL... R>ST cm_ref<T1,T2,R...>:cmR3<void,T1,T2,R...>{};
//[common.type]
TP<CL...>ST cm_ty;
TP<CL... Ts>using cm_ty_t=TY cm_ty<Ts...>::type;
TP<CL T,CL U>CEXP BL SameDecayedV=is_same_v<T,decay_t<T>>&&is_same_v<U,decay_t<U>>;
TP<CL T,CL U>using TerRetT=decay_t<DCLT(0?DCLV(T):DCLV(U))>;
TP<CL,CL,CL=void>ST cmT2{};
TP<CL T,CL U>ST cmT2<T,U,enable_if_t<!SameDecayedV<T,U>>>:cm_ty<decay_t<T>,decay_t<U>>{};
TP<CL T,CL U>ST cmT2<T,U,enable_if_t<SameDecayedV<T,U>&&Exist<TerRetT,T,U>>>:ty_id<TerRetT<T,U>>{};
TP<CL T,CL U>ST cmT2<T,U,enable_if_t<SameDecayedV<T,U>&&!Exist<TerRetT,T,U>&&Exist<CondResT,cref_t<T>,cref_t<U>>>>:ty_id<decay_t<CondResT<cref_t<T>,cref_t<U>>>>{};
TP<CL T>ST cm_ty<T>:cm_ty<T,T>{};
TP<CL T,CL U>ST cm_ty<T,U>:cmT2<T,U>{};
TP<CL,CL...>ST cmT3{};
TP<CL T1,CL T2,CL...R>ST cmT3<void_t<cm_ty_t<T1,T2>>,T1,T2,R...>:cm_ty<cm_ty_t<T1,T2>,R...>{};
TP<CL T1,CL T2,CL... R>ST cm_ty<T1,T2,R...>:cmT3<void,T1,T2,R...>{};
//[invoke]
NP invoke_{
TP<CL>CEXP BL isRW=0;
TP<CL T>CEXP BL isRW<reference_wrapper<T>> =1;
TpReq(CL B,CL T,CL D,CL...A)(is_function_v<T>&&is_base_of_v<B,decay_t<D>>)
AC impl(T B::*f,D&&r,A&&...a)NOEXP_DCLT_RET((FWD(r).*f)(FWD(a)...))
TpReq(CL B,CL T,CL R,CL...A)(is_function_v<T>&&isRW<decay_t<R>>)
AC impl(T B::*f,R&&r,A&&...a)NOEXP_DCLT_RET((r.get().*f)(FWD(a)...))
TpReq(CL B,CL T,CL P,CL...A)(is_function_v<T>&&!isRW<decay_t<P>>&&!is_base_of_v<B,decay_t<P>>)
AC impl(T B::*f,P&&p,A&&...a)NOEXP_DCLT_RET(((*FWD(p)).*f)(FWD(a)...))
TpReq(CL B,CL T,CL D)(is_function_v<T>&&is_base_of_v<B,decay_t<D>>)
AC impl(T B::*d,D&&r)NOEXP_DCLT_RET(FWD(r).*d)
TpReq(CL B,CL T,CL R)(!is_function_v<T>&&isRW<decay_t<R>>)
AC impl(T B::*d,R&&r)NOEXP_DCLT_RET(r.get().*d)
TpReq(CL B,CL T,CL P)(!is_function_v<T>&&!isRW<decay_t<P>>&&!is_base_of_v<B,decay_t<P>>)
AC impl(T B::*d,P&&p)NOEXP_DCLT_RET((*FWD(p)).*d)
TpReq(CL F,CL...A)(!is_member_pointer_v<decay_t<F>>)
AC impl(F&&f,A&&...a)NOEXP_DCLT_RET(FWD(f)(FWD(a)...))
ST fn { TP<CL F,CL...A>auto COP()(F&&f,A&&...a)const NOEXP_DCLT_RET(impl(FWD(f),FWD(a)...)) };
}//invoke_
In_Rgs(In_cpo(IC invoke_::fn invoke;))
TP<CL T>lst<T>mk_lst(lst<T> i)NOEXP_RET(i)
TP<CL,CL,CL...>ST Hinv_res{};
TP<CL F,CL...A>ST Hinv_res<void_t<DCLT(Rg invoke(DCLV(F),DCLV(A)...))>,F,A...>{
using type=DCLT(Rg invoke(DCLV(F),DCLV(A)...));
};
TP<CL F,CL...A>ST inv_res:Hinv_res<void,F,A...>{};
TP<CL F,CL...A>using inv_res_t=TY inv_res<F,A...>::type;

//[concept.invocable]
ST invocable_concept {
// #if (defined(__clang_major__) &&(defined(__apple_build_version__) ||__clang_major__<7))
// TP<CL F,CL...A>auto freq(F&&f,A&&...a)->inv_res_t<F,A...>;
// #else
TP<CL F,CL...A>auto freq(F&&f,A&&...a)->DCLT(Rg invoke(FWD(f),FWD(a)...));
// #endif
};
TP<CL F,CL...A>concept invocable=CpRef(invocable,F,A...);
TP<CL T,CL U>concept same=same_as<rmv_cvr_t<T>,rmv_cvr_t<U>>;
#define def_call(Na,FL) TP<CL...A>auto COP()(A&&...a) FL NOEXP_DCLT_RET(call((Na FL)*this,FWD(a)...))
#define def_init(Na,FL) TP<CL T,CL...A>auto COP()(initializer_list<T>&&i,A&&...a) FL NOEXP_DCLT_RET(call((Na FL)*this,FWD(i),FWD(a)...))
#define def_sub(Na,FL) TP<CL A>auto COP[](A&&a) FL NOEXP_DCLT_RET(sub((Na FL)*this,FWD(a)))
#define def_all(S,Na) def_##S(Na,&)def_##S(Na,&&)def_##S(Na,const&)def_##S(Na,const&&)
ST deleted_t{};
TP<CL...>CL first_of{};TP<CL...F>first_of(F...) ->first_of<F...>;
TP<CL F,CL...T>ST first_of<F,T...>{
using R=first_of<T...>;
NUA F f;NUA R r;
TP<CL S,CL...A,BL W=invocable<like_t<F,S&&>,A...>,CL X=like_t<cd_t<W,F,R>,S&&>>
SAC call(S&&s,A&&...a)noexcept(is_nothrow_invocable_v<X,A...>)->inv_res_t<X,A...>
{if CEXP(W)RET(Rg invoke(FWD(s).f,FWD(a)...))else RET(Rg invoke(FWD(s).r,FWD(a)...))}
TpReq(CL S,CL...A)(invocable<like_t<F,S&&>,A...>&&same_as<inv_res_t<like_t<F,S&&>,A...>,deleted_t>)VC call(S&&s,A&&...)=delete;
public:first_of()=default;CEXP first_of(F f,T...t):f(move(f)),r(move(t)...){}
def_all(call,first_of)
};
#define Bind(Na,_TYPE_,...) TP<CL F,CL...T>ST Na{TpReq(CL X,CL...Y)(!same<Na,X>)CEXP Na(X&&x,Y&&...y):f(FWD(x)),a(FWD(y)...){}\
TP<CL S,CL...X,CL FF=F>SAC call(S&&s,X&&...x)noexcept(is_nothrow_invocable_v<like_t<FF,S&&>,_TYPE_>)\
->inv_res_t<like_t<FF,S&&>,_TYPE_>RET(apply([&](auto&&...a)RET(Rg invoke(FWD(s).f,__VA_ARGS__)),FWD(s).a))def_all(call,Na)\
NUA F f;NUA tuple<T...>a;};TP<CL F,CL...A>Na(F,A...)->Na<F,A...>;
Bind(bindF,Pack(T...,X...),FWD(a)...,FWD(x)...)Bind(bindB,Pack(X...,T...),FWD(x)...,FWD(a)...)
#undef Bind
TP<CL L,CL R>ST compose{
TP<CL X,CL Y>CEXP compose(X&&l,Y&&r):l(FWD(l)),r(FWD(r)){}
TP<CL S,CL...A>SAC call(S&&s,A&&...a)NOEXP_DCLT_RET(Rg invoke(FWD(s).r,Rg invoke(FWD(s).l,FWD(a)...)))def_all(call,compose)
private:L l;R r;};
TP<CL L,CL R>compose(L,R)->compose<L,R>;
TP<CL F>ST raco;
TP<CL X>raco(X)->raco<X>;
TP<CL F>ST raco{using Raco=raco;TP<CL>friend ST raco;raco()=default;TpReq(CL X)(!same<X,raco>)CEXP raco(X&&x):f(FWD(x)){}
SAC __pip__=[](auto&&l,auto&&r)NOEXP_DCLT_RET(compose(FWD(l),FWD(r)));
TpReq(CL L,CL R)(ReqType(TypeInner(Raco,L),TypeInner(Raco,R)))SAC pip(L&&l,R&&r)NOEXP_DCLT_RET(std::raco(__pip__(FWD(l).f,FWD(r).f)))
SAC call=first_of([](auto&&r,auto&&...a)NOEXP_DCLT_RET(Rg invoke(FWD(r).f,FWD(a)...)),
[](auto&&r,auto&&...a)NOEXP_DCLT_RET(bindB(FWD(r).f,FWD(a)...)));
SAC sub=[](auto&&r,auto&&i)NOEXP_DCLT_RET(bindF(FWD(r).f,FWD(i)));
def_all(sub,raco)def_all(call,raco)//def_all(init,raco)
private:F f;};
CpDef(is_raco,CL T)(TY T::Raco)();TP<CL T>concept is_raco=CpRef(is_raco,T);
CPO pipeline=[](auto&&l,auto&&r)DCLT_RET(l.pip(FWD(l),FWD(r)));
TP<CL L,CL R>auto COP|(L&&l,R&&r)NOEXP_DCLT_RET(Rg invoke(FWD(r),FWD(l)))
TP<CL L,CL R>auto COP|=(L&&l,R&&r)NOEXP_DCLT_RET(l=invoke(FWD(r),FWD(l)))
TP<CL L,CL R>auto COP<(L&&l,R&&r)NOEXP_DCLT_RET(Rg invoke(FWD(l),FWD(r)))
TP<CL L,CL R>auto COP<<(L&&l,R&&r)NOEXP_DCLT_RET(FWD(l)[FWD(r)])
TP<CL L,CL R>auto COP%(L&&l,R&&r)NOEXP_DCLT_RET(Rg invoke(FWD(l),FWD(r)))
TP<CL L,CL R>auto COP^(L&&l,R&&r)NOEXP_DCLT_RET(compose(FWD(l),FWD(r)))
TP<CL T>decay_t<T>CEXP decay_copy(T&&t)NOEXP(DCLV(decay_t<T>&)=FWD(t))RET(FWD(t))
IC auto Auto=[](auto&&x)NOEXP_DCLT_RET(decay_copy(FWD(x)));
IC auto Move=[](auto&&x)NOEXP_DCLT_RET(move(FWD(x)));//[todo.fix.lvalue]
//[concepts]
CpDef(derived_from,CL D,CL B)()(Reqs(is_convertible_v<const volatile D*,const volatile B*>));
TP<CL D,CL B>concept derived_from=is_base_of_v<B,D>&&CpRef(derived_from,D,B);
//[concept.convertible]
CpDef(conv_to,CL From,CL To)(add_rvalue_reference_t<From>(&f)())(static_cast<To>(f()),);
TP<CL From,CL To>concept conv_to=is_convertible_v<From,To>&&CpRef(conv_to,From,To);
CpDef(cm_ref_with,CL T,CL U)()(
Reqs(same_as<cm_ref_t<T,U>,cm_ref_t<U,T>>)
Reqs(conv_to<T,cm_ref_t<T,U>>)
Reqs(conv_to<U,cm_ref_t<T,U>>)
);
TP<CL T,CL U>concept cm_ref_with=CpRef(cm_ref_with,T,U);
CpDef(common_with,CL T,CL U)()(
Reqs(same_as<cm_ty_t<T,U>,cm_ty_t<U,T>>)
static_cast<cm_ty_t<T,U>>(DCLV(T)),
static_cast<cm_ty_t<T,U>>(DCLV(U)),
Reqs(cm_ref_with<add_lvalue_reference_t<const T>,add_lvalue_reference_t<const U>>)
Reqs(cm_ref_with<add_lvalue_reference_t<cm_ty_t<T,U>>,
cm_ref_t<add_lvalue_reference_t<const T>,add_lvalue_reference_t<const U>>>)
);
TP<CL T,CL U>concept common_with=CpRef(common_with,T,U);
CpDef(assignable_from,CL L,CL R)(L l,R&&r)(
RetReq(same_as,L)(l=FWD(r))
Reqs(cm_ref_with<const rmv_r_t<L>&,const rmv_r_t<R>&>)
);
TP<CL L,CL R>concept assignable_from=is_lvalue_reference_v<L>&&CpRef(assignable_from,L,R);
TP<CL T>concept destructible=is_nothrow_destructible_v<T>;
TP<CL T,CL...A>concept cst_from=destructible<T>&&is_constructible_v<T,A...>;
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
In_Rgs(In_cpo(CPO swap=swap_fn{};))
CpDef(swappable,CL T)(T&a,T&b)(Rg swap(a,b),);
TP<CL T>concept swappable=CpRef(swappable,T);
CpDef(swappable_with,CL T,CL U)(T&&t,U&&u) (
Reqs(cm_ref_with<T,U>)
Rg swap(FWD(t),FWD(t)),Rg swap(FWD(u),FWD(u)),Rg swap(FWD(t),FWD(u)),Rg swap(FWD(u),FWD(t)),
);
TP<CL X,CL Y>concept swappable_with=CpRef(swappable_with,X,Y);
TP<CL T>concept bool_ts_impl=conv_to<T,bool>;
CpDef(bool_ts,CL T) (T&&t)(Cret1(bool_ts_impl,!FWD(t)));
TP<CL T>concept boolean_testable=bool_ts_impl<T>&&CpRef(bool_ts,T);
#define BLT(...) Cret1(boolean_testable,__VA_ARGS__)
CpDef(weakly_eq_cmp_with,CL T,CL U)(const rmv_r_t<T>&t,const rmv_r_t<U>&u)
(BLT(t==u)BLT(t!=u)BLT(u==t)BLT(u!=t));
TP<CL T,CL U>concept weakly_eq_cmp_with=CpRef(weakly_eq_cmp_with,T,U);
TP<CL T>concept eq_cmp=weakly_eq_cmp_with<T,T>;
CpBl(eq_cmp_with,CL T,CL U)(eq_cmp<T>&&eq_cmp<U>&&weakly_eq_cmp_with<T,U>&&
cm_ref_with<const rmv_r_t<T>&,const rmv_r_t<U>&>&&eq_cmp<cm_ref_t<const rmv_r_t<T>&,const rmv_r_t<U>&>>);
TP<CL T,CL U>concept eq_cmp_with=CpRef(eq_cmp_with,T,U);
CpDef(par_ord_with,CL T,CL U)(const rmv_r_t<T>& t,const rmv_r_t<U>& u)
(BLT(t>u)BLT(t<u)BLT(t<=u)BLT(t>=u)BLT(u<t)BLT(u>t)BLT(u<=t)BLT(u>=t));
TP<CL T,CL U>concept par_ord_with=CpRef(par_ord_with,T,U);
TP<CL T>concept tot_ord=eq_cmp<T>&&par_ord_with<T,T>;
CpDef(tot_ord_with,CL T,CL U)()(
Reqs(tot_ord<T>&&tot_ord<U>&&eq_cmp_with<T,U>&&par_ord_with<T,U>)
Reqs(tot_ord<cm_ref_t<const rmv_r_t<T>&,const rmv_r_t<U>&>>)
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
TP<CL F,CL...A>concept predicate=CpRef(predicate,F,A...);
TP<CL R,CL T,CL U>concept relation=predicate<R,T,T>&&predicate<R,U,U>&&predicate<R,T,U>&&predicate<R,U,T>;

//[func-tools]
TP<CL,TPP=map>ST Hmemo{};
TP<TPP M,CL R,CL...A>ST Hmemo<R(A...),M>{
TP<CL F>ST fn{
fn(fn&&)=default;fn(F f):f(move(f)){}using T=tuple<decay_t<A>...>;mutable M<T,R> m;F f;
TP<CL...S>R const&operator()(S&&...s)const{
T t{s...};auto i=m.find(t);if(i==m.end())i=m.emplace((T&&)t,invoke(f,ref(*this),(S&&)s...)).first;RET(i->second)
}
};
TP<CL F>fn(F)->fn<F>;
};
#define memo(...) Hmemo<__VA_ARGS__>::fn
TP<CL F>ST Yc{
F f;TP<CL L>Yc(L&&l):f(FWD(l)){}
TP<CL...A>auto COP()(A&&...a)const NOEXP_DCLT_RET(f(*this,(A&&)a...))
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
TP<CL R>ST cast_fn{TP<CL T>auto COP()(T&&t)const NOEXP_DCLT_RET(static_cast<R>(FWD(t)));};
TP<CL R>CPO as=cast_fn<R>{};
NP ranges{
using std::data;
inline NP cpo {
using less=raco<::less<>>;
using greater=raco<::greater<>>;
using less_equal=raco<::less_equal<>>;
using greater_equal=raco<::greater_equal<>>;
using equal_to=raco<::equal_to<>>;
using not_equal_to=raco<::not_equal_to<>>;
using plus=raco<::plus<>>;
using minus=raco<::minus<>>;
IC auto empty=[](auto&&x)DCLT_RET(std::empty(FWD(x)));
IC auto size=[](auto&&x)DCLT_RET(std::size(FWD(x)));
IC auto begin=[](auto&&x)DCLT_RET(std::begin(FWD(x)));
IC auto end=[](auto&&x)DCLT_RET(std::end(FWD(x)));
NP i_mv_{
void iter_move();
IC auto fn=first_of([](auto&&i)NOEXP_DCLT_RET(iter_move(*FWD(i))),[](auto&&i)NOEXP_DCLT_RET(move(*FWD(i))));
}
IC auto iter_move=i_mv_::fn;
NP get_{
TP<size_t,CL T>void get(T&&)=delete;
TP<size_t N>IC auto fn=first_of([](auto&&t)NOEXP_DCLT_RET(FWD(t).TP get<N>()),[](auto&&t)NOEXP_DCLT_RET(get<N>(FWD(t))));
}
TP<size_t N> IC auto get=get_::fn<N>;
}
}//ranges
CPO Begin=Rg begin;CPO End=Rg end;CPO Size=Rg size;CPO Empty=Rg empty;


NP Tp{
#define Seq index_sequence
#define make_Seq make_index_sequence
TP<CL T>using idxT=make_Seq<tuple_size_v<rmv_cvr_t<T>>>;
TP<CL...A>ST Htorp:ty_id<tuple<A...>>{};TP<CL A,CL B>ST Htorp<A,B>:ty_id<pair<A,B>>{};TP<CL...A>using tp_pa=TY Htorp<A...>::type;

TP<CL F,CL L,CL R,size_t...i>AC t_impl(F&&f,L&&l,R&&r,Seq<i...>)
RET(tp_pa<DCLT(invoke(FWD(f),get<i>(FWD(l)),get<i>(FWD(r))))...>(invoke(FWD(f),get<i>(FWD(l)),get<i>(FWD(r)))...))
TP<CL F,CL L,CL R,size_t...i>VC f_impl(F&&f,L&&l,R&&r,Seq<i...>)RET((invoke(FWD(f),get<i>(FWD(l)),get<i>(FWD(r))),...))
TP<CL T,CL O,CL P,size_t...x>size_t CEXP fd_impl(T&&t,size_t i,size_t j,O o,P p,Seq<x...>){
size_t s=0;bool y=0;
(void(i<=x&&x<j?y?s=Rg invoke(o,s,invoke(p,get<x>(FWD(t)))):(y=1,s=invoke(p,get<x>(FWD(t)))):s),...);
return s;
}

TP<CL...T>using back=tuple_element_t<sizeof...(T)-1,tuple<T...>>;

TP<CL F,CL Tp>AC for_(F&&f,Tp&&tp) { apply([&](auto&&...a){ (invoke(f,FWD(a)),...);},FWD(tp) );}
TP<CL F,CL L,CL R>AC for_(F&&f,L&&l,R&&r)RET(tpf_impl(FWD(f),FWD(l),FWD(r),idxT<L>{}))
TP<CL F,CL Tp>AC tran(F&&f,Tp&&tp)RET(apply([&](auto&&...a)RET(tp_pa<inv_res_t<F&,DCLT(a)>...>(invoke(f,FWD(a))...)),FWD(tp)))
TP<CL F,CL L,CL R>AC tran(F&&f,L&&l,R&&r)RET(t_impl(FWD(f),FWD(l),FWD(r),idxT<L>{}))
TP<CL T,CL O,CL P>AC fold(T&&t,size_t i,size_t j,O o,P p)RET(fd_impl(FWD(t),i,j,ref(o),ref(p),idxT<T>{}))
TP<CL T>T HH();
TP<CL T>CPO Hval=[](auto)->T RET(HH<T>());
TP<CL X,size_t N>using repeat=decltype(tran(Hval<X>,array<int,N>{}));
}
TP<CL...A>VC swap(const tuple<A...>&i,const tuple<A...>&j){Tp::for_(Rg swap,i,j);}
ST idt{TP<CL T>DCLT(auto)COP()(T&&t)const RET((T&&)t)};
TP<CL C=less<>,CL P=idt>ST proj_cmp{
TP<CL X,CL Y>proj_cmp(X&&x,Y&&y):c((X&&)x),p((Y&&)y){}
TP<CL T,CL U>BL COP()(T&&t,U&&u)const RET(Rg invoke(c,Rg invoke(p,(T&&)t),Rg invoke(p,(U&&)u)))
C c;P p;
};
TP<CL C,CL P>proj_cmp(C,P)->proj_cmp<C,P>;

//[iterator.primitives]
using ip_tag=input_iterator_tag;
using fw_tag=forward_iterator_tag;
using bd_tag=bidirectional_iterator_tag;
using ra_tag=random_access_iterator_tag;
ST ct_tag:ra_tag{};
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
// TP<CL T>ST rdtr<const T>:rdtr<T>{};
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
TP<CL T>AC iter_concept_impl(){
if CEXP(is_pointer_v<T>) return ct_tag{};
else if CEXP(has_iter_concept<T>) return TY T::iterator_concept{};
else if CEXP(has_iter_tag<T>) 
return TY iterator_traits<T>::iterator_category{};
}
TP<CL T>using iter_concept=DCLT(iter_concept_impl<T>());
CpDef(can_reference,CL I)(I&)();
TP<CL I>concept can_reference=CpRef(can_reference,I);
//[iterator.concept]
CpDef(ind_read,CL I,CL V=iv_t<I>,CL R=ir_t<I>,CL RR=irr_t<I>)(const I i)(
Cret(same_as,*i)(R)Cret(same_as,Rg iter_move(i))(RR)
Creq(cm_ref_with<R&&,V&>)Creq(cm_ref_with<R&&,RR&&>)Creq(cm_ref_with<RR&&,const V&>)
);
TP<CL I>concept ind_rd=CpRef(ind_read,rmv_cvr_t<I>);
CpDef(ind_wri,CL O,CL T)(O&&o,T&&t)(*o=FWD(t),*FWD(o)=FWD(t),);
TP<CL I>using ic_t=cm_ref_t<ir_t<I>,iv_t<I>&>;
TP<CL O,CL T>concept ind_wr=CpRef(ind_wri,O,T);
//[iterator.concept.winc]
CpDef(winc,CL I)(I i)(
Creq(signed_integral<id_t<I>>)
Cret(same_as,++i)(I&)
i++,
);
TP<CL I>concept winc=movable<I>&&CpRef(winc,I);
ST df_t{};IC df_t df{};
IC ST unr_t{
#define H TpReq(CL I)(winc<I>)BL FCOP
H==(I,unr_t)RET(0)H!=(I,unr_t)RET(1)H==(unr_t,I)RET(0)H!=(unr_t,I)RET(1)
#undef H
}unr;
CpDef(inc,CL I)(I i)(Cret(same_as,i++)(I));
TP<CL I>concept incrementable=regular<I>&&winc<I>&&CpRef(inc,I);
CpDef(io_i,CL I)(I i) (Creq(can_reference<DCLT(*i)>));
TP<CL I>concept io_i=winc<I>&&CpRef(io_i,I);
TP<CL S,CL I>concept s_for=semiregular<S>&&io_i<I>&&weakly_eq_cmp_with<S,I>;
CpDef(sz_s_for,CL S,CL I)(const I&i,const S&s)(Cret(same_as,s-i)(id_t<I>)Cret(same_as,i-s)(id_t<I>));
TP<CL S,CL I>concept sz_s_for=s_for<S,I>&&CpRef(sz_s_for,S,I);
CpBl(ip_i,CL I)(derived_from<iter_concept<I>,ip_tag>);
TP<CL I>concept ip_i=io_i<I>&&CpRef(ip_i,I);
CpBl(fw_i,CL I)(derived_from<iter_concept<I>,fw_tag>);
TP<CL I>concept fw_i=ip_i<I>&&CpRef(fw_i,I);
CpBl(bd_i,CL I)(derived_from<iter_concept<I>,bd_tag>);
TP<CL I>concept bd_i=fw_i<I>&&CpRef(bd_i,I);
CpBl(ra_i,CL I)(derived_from<iter_concept<I>,ra_tag>);
TP<CL I>concept ra_i=bd_i<I>&&CpRef(ra_i,I);
CpBl(ct_i,CL I)(derived_from<iter_concept<I>,ct_tag>);
TP<CL I>concept ct_i=ra_i<I>&&CpRef(ct_i,I);
//[indirects]
CpDef(ind_ui,CL F,CL I,CL V=iv_t<I>&,CL R=ir_t<I>)()(
Creq(invocable<F&,V>&&invocable<F&,R>&&invocable<F&,ic_t<I>>)
Creq(cm_ref_with<inv_res_t<F&,V>,inv_res_t<F&,R>>)
);
TP<CL F,CL I>concept ind_ui=ind_rd<I>&&copy_cst<F>&&CpRef(ind_ui,F,I);
CpBl(ind_up,CL F,CL I)(predicate<F&,iv_t<I>&>&&predicate<F&,ir_t<I>>&&predicate<F&,ic_t<I>>);
TP<CL F,CL I>concept ind_up=ind_rd<I>&&copy_cst<F>&&CpRef(ind_up,F,I);
CpBl(ind_bp,CL F,CL I,CL J,CL VI=iv_t<I>&,CL VJ=iv_t<J>&,CL RI=ir_t<I>,CL RJ=ir_t<J>)
(predicate<F&,VI,VJ>&&predicate<F&,VI,RJ>&&predicate<F&,RI,VJ>&&predicate<F&,RI,RJ>&&predicate<F&,ic_t<I>,ic_t<J>>);
TP<CL F,CL I,CL J=I>concept ind_bp=ind_rd<I>&&ind_rd<J>&&copy_cst<F>&&CpRef(ind_bp,F,I,J);
CpBl(ind_rel,CL F,CL I,CL J)(
relation<F&,iv_t<I>&,iv_t<J>&>&&relation<F&,iv_t<I>&,ir_t<J>>&&
relation<F&,ir_t<I>,iv_t<J>&>&&relation<F&,ir_t<I>,ir_t<J>>&&relation<F&,ic_t<I>,ic_t<J>>
);
TP<CL F,CL I,CL J=I>concept ind_rel=ind_rd<I>&&ind_rd<J>&&copy_cst<F>&&CpRef(ind_rel,F,I,J);
TP<CL F,CL...I>using ind_res_t=inv_res_t<F,ir_t<I>...>;
TP<CL,CL,CL=int>ST projed{};
TP<CL I,CL P>ST projed<I,P,Req(ind_rd<I>&&ind_ui<P,I>)>:cond_v<rmv_cvr_t<ind_res_t<P&,I>>>{ind_res_t<P&,I>operator*()const;};
//[alg.req]
CpDef(ind_mov,CL I,CL O)()(Creq(ind_rd<I>)Creq(ind_wr<O,irr_t<I>>));TP<CL I,CL O>concept ind_mv=CpRef(ind_mov,I,O);
CpBl(ind_mv_sto,CL I,CL O)(ind_mv<I,O>&&ind_wr<O,iv_t<I>>&&movable<iv_t<I>>&&cst_from<iv_t<I>,irr_t<I>>&&assignable_from<iv_t<I>&, irr_t<I>>);
TP<CL I,CL O>concept ind_mv_sto=CpRef(ind_mv_sto,I,O);
TP<CL I,CL J,CL R,CL P=idt,CL Q=idt>concept ind_cmp=ind_bp<R,projed<I,P>,projed<J,Q>>;
NP ranges {
NP i_sw_{
TP<CL X,CL Y>void iter_swap(X,Y)=delete;
TpReq(CL I,CL J)(ind_rd<I>&&ind_rd<J>&&swappable_with<ir_t<I>,ir_t<J>>)AC us_sw(I&&i,J&&j)NOEXP_DCLT_RET(Rg swap(*FWD(i),*FWD(j)))
TpReq(CL X,CL Y)(ind_mv_sto<X,Y>&&ind_mv_sto<Y,X>)CEXP iv_t<X>it_exc_mv(X&&x, Y&&y)
noexcept(noexcept(iv_t<X>(move(x))&&noexcept(*x=iter_move(y)))){iv_t<X> old(iter_move(x));*x=iter_move(y);RET(old)}
IC auto fn=first_of(
[](auto&&i,auto&&j)NOEXP_DCLT_RET((void)iter_swap(FWD(i),FWD(j))),
[](auto&&i,auto&&j)NOEXP_DCLT_RET((void)us_sw(FWD(i),FWD(j))),
[](auto&&i,auto&&j)NOEXP_DCLT_RET((void)(*FWD(i)=it_exc_mv(FWD(j),FWD(i))))
);
}
In_cpo(IC raco iter_swap=i_sw_::fn;)
//[range.iter.op]
IC ST advance_fn{
TpReq(CL I)(io_i<I>)void COP()(I&i,id_t<I>n)const{if CEXP(ra_i<I>)i+=n;else{if(n>=0)while (n--)++i;else if CEXP(bd_i<I>)while(n++)--i;}}
TpReq(CL I,CL S)(s_for<S,I>)void COP()(I&i,S s)const
{if CEXP(assignable_from<I&,S>) i=move(s);else if CEXP(sz_s_for<S,I>)(*this)(i,s-i);else while(i!=s)++i;}
TpReq(CL I,CL S)(s_for<S,I>)void COP()(I&i,id_t<I> n,S s)const{
    if CEXP(sz_s_for<S,I>){if(abs(n)>=abs(s-i))(*this)(i,s);else(*this)(i,n);}
    else{if(n<0){if CEXP(bd_i<I>)while(n++&&i!=s)--i;}else while(n--&&i!=s)++i;}
}
}advance;
IC ST next_fn {
TpReq(CL I)(io_i<I>) I COP()(I x)const RET(++x)
TP<CL I,CL...A>auto COP()(I x,A...a)const NOEXP_DCLT_RET(decay_copy((advance(x,a...),x)))
}next;
IC ST prev_fn {
TpReq(CL I)(bd_i<I>)I COP()(I x) const RET(--x)
TpReq(CL I,CL...A)(bd_i<I>)auto COP()(I x,id_t<I>n,A...a)const NOEXP_DCLT_RET(decay_copy((advance(x,n,a...),x)))
}prev;
//[ranges.range] concepts
CpDef(range,CL T)(T&t)(Begin(t),End(t),);
TP<CL T>concept range=CpRef(range,T);
TP<CL>IC BL enable_borrowed_rg=0;
TP<CL T>concept borrowed_rg=range<T>&&(is_lvalue_reference_v<T>|| enable_borrowed_rg<rmv_cvr_t<T>>);
TP<CL T>using i_t=DCLT(Begin(DCLV(T&)));
TP<CL T>using s_t=DCLT(End(DCLV(T&)));
TP<CL R>using rs_t=DCLT(Size(DCLV(R&)));
TP<CL R>using rd_t=id_t<i_t<R>>;
TP<CL R>using rv_t=iv_t<i_t<R>>;
TP<CL R>using rr_t=ir_t<i_t<R>>;
TP<CL R>using rrr_t=irr_t<i_t<R>>;
CpDef(sz_rg,CL T)(T&t)(Cret1(integral,Size(t)));
TP<CL T>concept sz_rg=range<T>&&CpRef(sz_rg,T);
IC ST dist_fn{
TpReq(CL I,CL S)(s_for<S,I>)id_t<I>COP()(I f,S l)const{if CEXP(sz_s_for<S,I>)RET(l-f)else{id_t<I>i=0;for(;f!=l;++f)++i;RET(i)}}
TpReq(CL R)(range<R>)rd_t<R>COP()(R&&r)const{if CEXP(sz_rg<R>)RET(size(r))else RET((*this)(ALL(r)))}
}distance;
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
//[range.copy]
ST copy_fn {
TP<CL I,CL S,CL O,CL P>
static O CEXP impl(I f,S l,O o,P p) { for (;f!=l;++f,++o)*o=invoke(p,*f);return o;}
TP<CL R,CL O,CL P=idt>
O COP ()(R&&r,O o,P p={}) const { return impl(begin(r),end(r),move(o),ref(p));}
};
IC copy_fn copy;
ST min_fn{
TpReq(CL R,CL C=less,CL P=idt)(ip_rg<R>&&ind_rel<C,projed<i_t<R>,P>>)
rv_t<R>COP()(R&&r,C c={},P p={})const{auto f=begin(r);auto l=end(r);rv_t<R>t=*f;proj_cmp w={ref(c),ref(p)};while(++f!=l)if(w(*f,t))t=*f;RET(t)}
TpReq(CL T,CL U,CL C=less,CL P=idt)(relation<C,T,U>)auto COP()(T&&t,U&&u,C c={},P p={})const
NOEXP_DCLT_RET(Rg invoke(c,Rg invoke(p,t),Rg invoke(p,u))?cm_ref_t<T,U>(FWD(t)):cm_ref_t<T,U>(FWD(u)))
};
IC raco min=min_fn{};
ST max_fn{
TpReq(CL R,CL C=less,CL P=idt)(ip_rg<R>&&ind_rel<C,projed<i_t<R>,P>>)
rv_t<R>COP()(R&&r,C c={},P p={})const{auto f=begin(r);auto l=end(r);rv_t<R>t=*f;proj_cmp w={ref(c),ref(p)};while(++f!=l)if(w(t,*f))t=*f;RET(t)}
// TP<CL T,CL C=less,CL P=idt>auto COP()(initializer_list<T>r,C c={},P p={})const DCLT_RET((*this)(r,move(c),ref(p)))
TP<CL T,CL U,CL C=less,CL P=idt>auto COP()(T&&t,U&&u,C c={},P p={})const
NOEXP_DCLT_RET(Rg invoke(c,Rg invoke(p,t),Rg invoke(p,u))?cm_ref_t<T,U>(FWD(u)):cm_ref_t<T,U>(FWD(t)))
};
IC raco max=max_fn{};
IC raco abs=[](auto x)NOEXP_DCLT_RET(::abs(x));
//[alg.find]
IC ST find_if_fn {
TpReq(CL I,CL S,CL F,CL P=idt)(s_for<S,I>)I COP()(I f,S l,F x,P p={})const{for(;f!=l;++f)if(invoke(x,invoke(p,*f)))break;return f;}
TpReq(CL R,CL F,CL P=idt)(ip_rg<R>)i_t<R> COP()(R&&r,F x,P p={})const RET((*this)(begin(r),end(r),move(x),move(p)))
} find_if;
IC ST find_if_not_fn{
TpReq(CL R,CL Pr,CL P=idt)(ip_rg<R>) 
auto COP()(R&&r,Pr pr,P p={})const RET(find_if(begin(r),end(r),not_fn(ref(pr)),ref(p)))
} find_if_not;
IC ST adjacent_find_fn{
TP<CL I,CL S,CL Pr,CL P>CEXP static I impl(I f,S l,Pr pr,P p){
if(f==l)RET(f)auto w=proj_cmp(ref(pr),ref(p));
for(auto n=next(f);n!=l;++n,++f)if(w(*f,*n))break;return f;
}
TpReq(CL R,CL C=equal_to,CL P=idt)(fw_rg<R>&&ind_bp<C,projed<i_t<R>,P>>)
auto COP()(R&&r,C c={},P p={})const RET(impl(ALL(r),ref(c),ref(p)))
TpReq(CL I,CL S,CL C=equal_to,CL P=idt)(fw_i<I>&&s_for<S,I>&&ind_bp<C,projed<I,P>>)
auto COP()(I f,S l,C c={},P p={})const RET(impl(move(f),move(l),ref(c),ref(p)))
} adjacent_find;
IC ST sort_fn{
TP<CL I,CL S,CL C,CL P>
static CEXP I impl(I f,S l,C c,P p){auto r=Rg next(f,l);::sort(f,r,proj_cmp(ref(c),ref(p)));return r;}
TpReq(CL R,CL C=less,CL P=idt)(ra_rg<R>)//todo sortable
DCLT(auto) COP()(R&&r,C c={},P p={})const RET(impl(Begin(r),End(r),ref(c),ref(p)))
}sort;

ST fold_fn{
CpBl(ind_lf_impl,CL F,CL T,CL I,CL U)(movable<T>&&movable<U>&&conv_to<T,U>&&assignable_from<U&,inv_res_t<F&,U,ir_t<I>>>);
CpBl(ind_lf,CL F,CL T,CL I,CL X=inv_res_t<F&,T,ir_t<I>>)(copy_cst<F>&&ind_rd<I>&&conv_to<X,decay_t<X>>&&CpRef(ind_lf_impl,F,T,I,decay_t<X>));
TpReq(CL I,CL T,CL S=I,CL P=idt,CL F=plus,CL U=rmv_cvr_t<inv_res_t<F&,T,ind_res_t<P&,I>>>)(ip_i<I>&&s_for<S,I>&&CpRef(ind_lf,F,T,projed<I,P>))
U COP()(I f,S l,T t,F o,P p)const{if(f==l)RET(U(move(t)))U a=invoke(o,move(t),invoke(p,*f));while(++f!=l)a=invoke(o,move(a),invoke(p,*f));RET(a)}
TpReq(CL R,CL T,CL F=plus,CL P=idt)(ip_rg<R>&&CpRef(ind_lf,F,T,projed<i_t<R>,P>))
auto COP()(R&&r,T t,F o={},P p={})const DCLT_RET((*this)(begin(r),end(r),move(t),ref(o),ref(p)))
};
IC raco fold=fold_fn{};
//[interfaces]
TP<CL D>CL VF{
#define B(FL)CEXP FL D&d()FL noexcept RET((FL D&)*this)
B()B(const)
#undef B
public:using __interface=VF;
#define B(FL) LazyT(D,fw_rg<FL t>)CEXP BL empty()FL RET(begin(d())==end(d()))
B()B(const)
#undef B
#define B(FL) LazyT(D,ReqExpr(Rg empty(DCLV(t&))))ECOP BL()FL RET(!Rg empty(d()))
B()B(const)
#undef B
//[todo->DCLT simplify?]
#define B(FL) LazyT(D,ReqExpr(range<FL t>&&ct_i<i_t<FL t>>))AC data()FL->DCLT(&*Begin(DCLV(const t&)))RET(&*begin(d()))
B()B(const)
#undef B
#define B(FL) LazyT(D,fw_rg<FL t>&&sz_s_for<s_t<FL t>,i_t<FL t>>)AC size()FL RET(End(d())-Begin(d()))
B()B(const)
#undef B
#define B(FL) LazyT(D,fw_rg<FL t>)CEXP DCLT(auto)front()FL RET(*begin(d()))
B()B(const)
#undef B
#define B(FL) LazyT(D,bd_rg<FL t>&&cm_rg<FL t>)CEXP DCLT(auto)back()FL RET(*prev(end(d())))
B()B(const)
#undef B
#define B(FL) LazyT(D,ra_rg<FL t>)DCLT(auto)COP[](rd_t<t>n) FL RET(begin(d())[n])
B()B(const)
#undef B
#define B(FL,R) LazyT(D,ReqExpr(DCLV(t&).b_))R base()FL RET((d().b_))
B(const&,DCLT(auto))B(&&,auto)
#undef B
#define B(FL) TP<size_t I>auto get() FL {if CEXP (I==0)RET(begin(d()))else RET(end(d())) }
B(&)B(&&)B(const&)B(const&&)
#undef B
};
TP<CL I,CL Tg,CL D,CL V,CL Ref>CL IF{//Need:adv inc dec,friend:dif lt eq:lt:df_t
#define TgD(v)static IC BL v=derived_from<Tg,v##_tag>;
TgD(fw)TgD(bd)TgD(ra)
#undef TgD
using R=I&;using CR=const I&;
R CEXP d()RET(R(*this))CR CEXP d()const RET(CR(*this))
#define RT(...) { __VA_ARGS__;return R(*this);}
public:using pointer=void;using iterator_category=Tg;using iterator_concept=Tg;using difference_type=D;using value_type=V;using reference=Ref;
#define B(FL,R) LazyT(I,ReqExpr(DCLV(t&).b_))R base()FL RET((d().b_))
B(const&,DCLT(auto))B(&&,auto)
#undef B
#define Sp(OP) {auto a=*this;OP*this;return (I&)a;}
R COP++()RT(d().inc())auto COP++(int){if CEXP(fw)Sp(++)else++*this;}
LazyT(I,bd)R COP--()RT(d().dec())LazyT(I,bd)I COP--(int)Sp(--)
#undef Sp
LazyT(I,ra)R COP+=(D n)RT(d().adv(n))LazyT(I,ra)R COP-=(D n)RT(d().adv(-n))
LazyT(I,ra)I FCOP+(const IF&i,D n){I j=i.d();R(j)+=n;return j;}LazyT(I,ra)I FCOP+(D n,const IF&i)RET(i+n)
LazyT(I,ra)I FCOP-(const IF&i,D n){I j=i.d();R(j)-=n;return j;}LazyT(I,ra)D FCOP-Crefp(IF)RET(dif(i.d(),j.d()))
LazyT(I,ra)DCLT(auto)COP[](D n)RET(*(*this+n).d())
#define Def(Na,X) ReqExpr(Na(DCLV(X),DCLV(X)))
LazyT(I,Def(eq,t&))BL FCOP==Crefp(IF) RET(eq(i.d(),j.d()))LazyT(I,Def(eq,t&))BL FCOP!=Crefp(IF) RET(!(i==j))
#define Deff LazyT(I,ra&&Def(lt,const t&))
Deff BL FCOP<Crefp(IF) RET(lt(i.d(),j.d()))Deff BL FCOP>Crefp(IF) RET(j<i)
Deff BL FCOP<=Crefp(IF) RET(!(j<i))Deff BL FCOP>=Crefp(IF) RET(!(i<j))
#undef Deff

#define AA (const IF&i,df_t)
#define BB (df_t,const IF&i)
#define EE RET(i.d().rte())
#define NN RET(!i.d().rte())
#define Deff LazyT(I,ReqExpr(DCLV(t&).rte()))
Deff BL FCOP==AA EE Deff BL FCOP==BB EE Deff BL FCOP!=AA NN Deff BL FCOP!=BB NN
#undef Deff
#undef NN
#undef EE
#define Deff LazyT(I,ReqExpr(DCLV(t&).dte()))D FCOP-
Deff AA RET(i.d().dte())Deff BB RET(-i.d().dte())
#undef Deff
#undef AA
#undef BB
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
#define Def TpReq(CL I,CL t=S)(ReqExpr(DCLV(t&).dif(DCLV(I&)))) auto FCOP-
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
CpBl(sp_vw,CL V)(view<V>&&range<const V>&&same_as<i_t<V>,i_t<const V>>&&same_as<s_t<V>,s_t<const V>>);
TP<CL V>concept sp_vw=CpRef(sp_vw,V);
CpDef(has_arrow,CL I)(I i)(i.operator->(),);
TP<CL I>concept has_arrow=ip_i<I>&&(is_pointer_v<I>|| CpRef(has_arrow,I));
TP<CL T,CL U>concept different_from=!same_as<rmv_cvr_t<T>,rmv_cvr_t<U>>;
ST dangling { dangling()noexcept=default;TP<CL...A>dangling(A&&...){} };
//[wrappers]
#define US using P=optional<T>;using P::optional;using P::reset;using P::operator=;
#define DF box(const box&)=default;box(box&&)=default;
TP<CL T,CL=int>ST box:optional<T>{
US
LazyT(T,!df_init<T>)box()=delete;
LazyT(T,df_init<T>)CEXP box()noexcept(is_nothrow_default_constructible_v<T>):optional<T>{in_place}{}
#define AS(CV) box&operator=(box CV u)RET_THIS(\
if CEXP(assignable_from<T&,T CV>)P::operator=((optional<T>CV)u);else if(this!=&u){if(u)this->emplace((T CV)*u);else reset();})
AS(&&)AS(const&)DF
#undef AS
};
TP<CL T>ST box<T,Req(copyable<T>||(is_nothrow_move_constructible_v<T>&&is_nothrow_copy_constructible_v<T>))>{
EC box(const T&t)noexcept(is_nothrow_copy_constructible_v<T>):t(t){}
EC box(T&&t)noexcept(is_nothrow_copy_constructible_v<T>):t(move(t)){}
TpReq(CL...A)(cst_from<T,A...>)EC box(in_place_t,A&&...a)noexcept(is_nothrow_constructible_v<T,A...>):t(FWD(a)...){}
box()=default;CEXP box&operator=(T z)RET_THIS(t=move(z);)
#define AS(CV) box&operator=(box CV r)RET_THIS(if CEXP(copyable<T>)t=(T CV)r.t;else if(this!=&r)t.~T(),new(&t)T((T CV)*r);)
AS(const&)AS(&&)DF
#undef AS
SC BL has_value()noexcept RET(1)
#define AX(a,b,c,d) CEXP c T a operator b()c noexcept RET(d t)
AX(&,*,,)AX(&,*,const,)AX(*,->,,&)AX(*,->,const,&)
#undef AX
private:T t;};
#undef DF
TP<CL T,CL=int>ST np_box{};
TP<CL T>ST np_box<T,Req(is_object_v<T>)>:optional<T>{
using P=optional<T>;
using P::operator=;
np_box()=default;
CEXP np_box(nullopt_t):P{}{}      
CEXP np_box(const np_box&)noexcept{}
CEXP np_box(np_box&& o)noexcept{o.reset();}
CEXP np_box&operator=(const np_box&o)noexcept RET_THIS(if(&o!=this)this->reset();)
CEXP np_box&operator=(np_box&&o)noexcept RET_THIS(this->reset();o.reset();)
TP<CL I>T&emplace_deref(const I&i){this->reset();return this->emplace(*i);}
};
TP<CL T>using c_box=np_box<T>;
//[range.subrange]
enum CL subrange_kind {sized,unsized};
TP<CL From,CL To>concept conv_to_non_slicing=
conv_to<From,To>&&!(is_pointer_v<decay_t<From>>&&is_pointer_v<decay_t<To>>&&
different_from<remove_pointer_t<decay_t<From>>,remove_pointer_t<decay_t<To>>>);
TP<CL I,CL S=I,subrange_kind K= sz_s_for<S,I>? subrange_kind::sized:subrange_kind::unsized>
CL subrange:public VF<subrange<I,S,K>>{
static_assert(io_i<I>);
static_assert(s_for<S,I>);
static_assert(K==subrange_kind::sized ||!sz_s_for<S,I>);
static CEXP BL StoreSize=(K==subrange_kind::sized &&!sz_s_for<S,I>);
using sz_t=make_unsigned_t<id_t<I>>;
public:subrange()=default;
TpReq(CL II)(conv_to_non_slicing<II,I>&&!StoreSize)CEXP subrange(II i,S s):i(move(i)),s{s}{}
TpReq(CL II)(conv_to_non_slicing<II,I>&&K==subrange_kind::sized)CEXP subrange(II i,S s,sz_t n):i(move(i)),s{s},sz{n}{}
TpReq(CL R)(borrowed_rg<R>&&conv_to_non_slicing<i_t<R>,I>&&conv_to<s_t<R>,S>&&StoreSize)
CEXP subrange(R&&r):subrange(r,Size(r)){}
TpReq(CL R)(!same<subrange,R>&&borrowed_rg<R>&&conv_to_non_slicing<i_t<R>,I>&&conv_to<s_t<R>,S>&&!StoreSize)
subrange(R&&r):subrange(Begin(r),End(r)){}
TpReq(CL R)(borrowed_rg<R>&&conv_to_non_slicing<i_t<R>,I>&&conv_to<s_t<R>,S>&&K==subrange_kind::sized)
CEXP subrange(R&&r,sz_t n):subrange(Begin(r),End(r),n){}
LazyT(I,copyable<I>)AC begin()const RET(i)
LazyT(I,!copyable<I>)AC begin()RET(move(i))
CEXP S end()const RET(s)
CEXP BL empty()const RET(i==s)
LazyV(K,K==subrange_kind::sized)CEXP sz_t size()const{if CEXP(StoreSize)return sz;else return to_unsigned(s-i);}
LazyT(I,same_as<iv_t<I>,char>)COP string_view()const RET({this->data(),size()})
private:I i;S s;NUA cd_t<StoreSize,sz_t,dangling>sz;
};
TpReq(CL I,CL S)(s_for<S,I>)subrange(I,S)->subrange<I,S>;
TpReq(CL I,CL S)(s_for<S,I>)subrange(I,S,make_unsigned_t<id_t<I>>)->subrange<I,S,subrange_kind::sized>;
TpReq(CL R)(borrowed_rg<R>)subrange(R&&)->subrange<i_t<R>,s_t<R>,
(sz_rg<R>|| sz_s_for<i_t<R>,s_t<R>>)?subrange_kind::sized:subrange_kind::unsized>;
TpReq(CL R)(borrowed_rg<R>)subrange(R&&,make_signed_t<rd_t<R>>)->subrange<i_t<R>,s_t<R>,subrange_kind::sized>;
}//ranges

#define Tps(Tmp,...)\
TP<Tmp>ST tuple_size<Rg __VA_ARGS__>:integral_constant<size_t,2>{};\
TP<Tmp>ST tuple_element<0,Rg __VA_ARGS__>:ty_id<Rg i_t<Rg __VA_ARGS__>>{};\
TP<Tmp>ST tuple_element<0,const Rg __VA_ARGS__>:ty_id<Rg i_t<const Rg __VA_ARGS__>>{};\
TP<Tmp>ST tuple_element<1,Rg __VA_ARGS__>:ty_id<Rg s_t<Rg __VA_ARGS__>>{};\
TP<Tmp>ST tuple_element<1,const Rg __VA_ARGS__>:ty_id<Rg s_t<const Rg __VA_ARGS__>>{};
Tps(Pack(CL I,CL S,Rg subrange_kind K),subrange<I,S,K>)
CpDef(ind_sw,CL I,CL J)(I&i,J&j)(Rg iter_swap(i,j),Rg iter_swap(j,i),Rg iter_swap(i,i),Rg iter_swap(j,j),);
TP<CL I,CL J=I>concept ind_sw=ind_rd<I>&&ind_rd<J>&&CpRef(ind_sw,I,J);
#define F Rg IF<counted_iterator<I>,iter_concept<I>,id_t<I>,iv_t<I>,ir_t<I>>
TpReq(CL I)(io_i<I>)ST counted_iterator:F{
counted_iterator()=default;CEXP counted_iterator(I i,id_t<I>n):b_(i),n_(n){}
DCLT(auto)COP*()RET(*b_)DCLT(auto)COP*()const RET(*b_)
#define NB Crefp(counted_iterator)
FC irr_t<I> iter_move(const counted_iterator&i)NOEXP_RET(Rg iter_move(i.b_))
FC void iter_swap NB NOEXP_RET(Rg iter_swap(i.b_,j.b_))
private:friend F;I b_;id_t<I>n_;
VC inc(){++b_;--n_;} LazyT(I,1)VC dec(){--b_;++n_;}VC adv(id_t<I>n){b_+=n;n_-=n;}FC id_t<I> dif NB RET(j.n_-i.n_)
FC BL eq NB RET(i.n_==j.n_)FC BL lt NB RET(i.n_>j.n_)BC rte()const RET(!n_)CEXP id_t<I>dte()const RET(-n_)
};
#undef F
#undef NB
#define Def_Vw_Adp(Name) In_Vws(IC raco Name=[](auto&&...a)NOEXP_DCLT_RET(Name##_view(FWD(a)...));)
#define Def_Vw_Adp_(X,...) In_Vws(IC raco X=__VA_ARGS__;)
NP ranges{
//[single.view]
TpReq(CL T)(is_object_v<T>&&copy_cst<T>)ST single_view:VF<single_view<T>>{
TpReq(CL U)(same_as<rmv_cvr_t<U>,T>)CEXP explicit single_view(U&&u):v_(FWD(u)){}
TpReq(CL...A)(cst_from<T,A...>)CEXP explicit single_view(in_place_t l,A&&...a):v_{l,FWD(a)...}{}
#define Y(Na,Cv,...) CEXP Cv T*Na()Cv noexcept RET(__VA_ARGS__)
#define X(Na,Cv,...) Y(Na,Cv,data() __VA_ARGS__)
X(begin,)X(begin,const,)X(end,,+1)X(end,const,+1)
#undef X
static CEXP size_t size()noexcept RET(1)
Y(data,,v_.operator->())Y(data,const,v_.operator->())
#undef Y
private:box<T>v_;
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
TP<CL W,CL B=unr_t>CL iota_view:public VF<iota_view<W,B>>{
using Tg=cd_t<advanceable<W>,ra_tag,cd_t<decrementable<W>,bd_tag,cd_t<incrementable<W>,fw_tag,ip_tag>>>;
using D=id_t<W>;
TP<CL I>using F=IF<I,Tg,D,W,W>;
ST S;ST I:public F<I>{
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
S()=default;CEXP explicit S(B b):b(b){}
private:B b;
CEXP BL eq(const I&i)const RET(b==i.v)LazyT(W,sz_s_for<B,W>)CEXP BL dif(const I&i)const RET(b-i.v)
};
W v;B b;
public:
iota_view()=default;
CEXP explicit iota_view(W v):v(v){}
CEXP iota_view(ty_id_t<W>v,ty_id_t<B>b):v(v),b(b){}
CEXP I begin() const { return I{v};}
AC end() const {
if CEXP(is_same_v<W,B>) return I{b};
else if CEXP(is_same_v<B,unr_t>) return unr;
else return S{b};
}
LazyT(W,same_as<W,B>|| (integral<W>&&integral<B>) || sz_s_for<B,W>) AC size() const {
if CEXP(is_integral_v<W>&&is_integral_v<B>)
return v<0 ? b<0 ? to_unsigned(-v)-to_unsigned(-b):to_unsigned(b) + to_unsigned(-v):to_unsigned(b)-to_unsigned(v);
else return to_unsigned(b-v);
}
};
TP<CL W,CL B>iota_view(W,B)->iota_view<W,B>;
Def_Vw_Adp(iota)
TP<BL C,CL T>using maybe_const=cd_t<C,const T,T>;
CpDef(str_ex,CL V,CL CT,CL Tr)(basic_istream<CT,Tr>&i,V&t)(i>>t,);
TpReq(CL V,CL CT,CL Tr)(movable<V>&&df_init<V>&&CpRef(str_ex,V,CT,Tr))
    CL basic_istream_view:public VF<basic_istream_view<V,CT,Tr>> {
basic_istream<CT,Tr>*s_;V v_;
ST I;using F=IF<I,ip_tag,ptrdiff_t,V,V&>;
ST I:F{
using P=basic_istream_view;P*p_;
public:I(P&p):p_(&p){}I(I&&)=default;I&operator=(I&&)=default;
DCLT(auto) COP*()const RET((p_->v_))
VC inc(){*p_->s_>>p_->v_;}BC rte()const RET(!*p_->s_)
};
public:EC basic_istream_view(basic_istream<CT,Tr>&i):s_(&i){}
CEXP I begin(){*s_>>v_;RET({*this})}CEXP df_t end()RET({})
};
TP<CL V,CL CT,CL Tr> auto istream_view(basic_istream<CT,Tr>&s)RET(basic_istream_view<V,CT,Tr>{s})
//[range.ref.view]
TpReq(CL R)(range<R>&&is_object_v<R>)CL ref_view:public VF<ref_view<R>>{
ST ref_req_concept{static void FUN(R&);static void FUN(R&&)=delete;TP<CL T>auto freq()->DCLT(FUN(DCLV(T)));};
R*r;
public:TpReq(CL T)(different_from<T,ref_view>&&conv_to<T,R&>&&CpRef(ref_req,T))
CEXP ref_view(T&&t):r(&(R&)(FWD(t))){}
CEXP R&base()const RET(*r)
AC begin() const RET(Begin(*r))
AC end() const RET(End(*r))
LazyT(R,ReqExpr(Rg empty(*DCLV(t))))CEXP BL empty()const RET(Rg empty(*r))
LazyT(R,sz_rg<R>)AC size()const RET(Size(*r))
LazyT(R,ct_rg<R>)AC data()const RET(Rg data(*r))
};
TP<CL R>ref_view(R&)->ref_view<R>;
TP<CL>IC BL init_ls=0;TP<CL T>IC BL init_ls<lst<T>> =1;
TpReq(CL R)(movable<R>&&!init_ls<R>)ST owning_view:VF<owning_view<R>>{
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
//[view.filter]
TpReq(CL V,CL P)(view<V>&&ip_rg<V>&&is_object_v<V>&&ind_up<P,i_t<V>>)CL filter_view:public VF<filter_view<V,P>>{
friend VF<filter_view<V,P>>;
using IV=i_t<V>;V b_;box<P> p_;c_box<IV>c_;
using Tg=cd_t<bd_rg<V>,bd_tag,cd_t<fw_rg<V>,fw_tag,ip_tag>>;
using R=rr_t<V>;
#define F IF<I,Tg,rd_t<V>,rv_t<V>,R>
ST S;CL I:public F{
friend F;friend S;IV b_;filter_view*p_;
#undef F
VC inc(){b_=find_if(move(++b_),End(p_->b_),ref(*p_->p_));}
LazyT(V,bd_rg<V>)VC dec(){do--b_;while(!invoke(*p_->p_,*b_));}
LazyT(V,eq_cmp<IV>)FC BL eq Crefp(I)RET(i.b_==j.b_)
public:I()=default;CEXP I(filter_view&p,IV b):p_(&p),b_(move(b)){}
R COP*()const RET(*b_)LazyT(IV,has_arrow<t>&&copyable<t>)R COP->()RET(b_)
DCLT(auto)FC iter_move(const I&i)NOEXP_RET(Rg iter_move(i.b_))
LazyT(V,ind_sw<IV>)FVC iter_swap Crefp(I)NOEXP_RET(Rg iter_swap(i.b_,j.b_))
};ST S:SF<S>{
S()=default;S(s_t<V>s):b_(move(s)){}
private:friend SF<S>;s_t<V>b_;BC eq(const I&i)const RET(i.b_==b_)
};
public:filter_view()=default;CEXP filter_view(V v,P p):b_(move(v)),p_(move(p)){}
I begin(){if(!c_.has_value())c_=find_if(b_,ref(*p_));RET({*this,*c_})}
auto end(){if CEXP(cm_rg<V>)RET(I{*this,End(b_)})else RET(S{End(b_)})}
};
TP<CL R,CL F>filter_view(R&&,F)->filter_view<Vw all_t<R>,F>;
Def_Vw_Adp(filter)
//[view.transform]
TpReq(CL V,CL F)(ip_rg<V>&&view<V>&&copy_cst<F>&&is_object_v<F>&&invocable<F&,rr_t<V>>&&can_reference<inv_res_t<F&,rr_t<V>>>)
CL transform_view:public VF<transform_view<V,F>>{
TP<BL>ST S;friend VF<transform_view<V,F>>;
#define B maybe_const<C,V>
#define D rd_t<B>
TP<BL C>using Tg=cd_t<ra_rg<B>,ra_tag,cd_t<bd_rg<B>,bd_tag,cd_t<fw_rg<B>,fw_tag,ip_tag>>>;
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
I()=default;CEXP I(P&p,Ty c):p_(&p),i_(move(c)){}LazyT(V,C&&conv_to<i_t<V>,Ty>)CEXP I(I<!C>i):i_(move(i.i_)),p_(i.p_){}
AC base()const&RET(i_)AC base()&&RET(move(i_))
DCLT(auto)COP*()const RET(Rg invoke(*p_->f_,*i_))
FC DCLT(auto)iter_move(const I&i)NOEXP(Rg invoke(*p_->f_,*i_)){if CEXP(is_lvalue_reference_v<DCLT(*i)>)RET(move(*i))return*i;}
LazyT(B,ind_sw<i_t<B>>)FC auto iter_swap Crefp(I)NOEXP_RET(Rg iter_swap(i.i_,j.i_))
};
TP<BL C>CL S:public SF<S<C>> {
TP<BL>friend ST S;friend SF<S<C>>;
using Pa=maybe_const<C,transform_view>;using Ty=s_t<B>;Ty s_;
#define Def(Na) TpReq(BL CC)(Na##s_for<Ty,i_t<maybe_const<CC,V>>>)
Def()BL eq(const I<CC>&i)const RET(s_==i.i_)Def(sz_)D dif(const I<CC>&i)const RET(s_-i.i_)
#undef D
#undef B
#undef Def
public:AC base()RET(s_)
S()=default;CEXP S(Ty s):s_(move(s)){}LazyT(V,C&&conv_to<s_t<V>,Ty>)CEXP S(S<!C>s):s_(move(s.s_)){}
};
V b_=V();box<F>f_;
public:
CEXP transform_view(V v,F f):b_(move(v)),f_(move(f)){}
CEXP I<0>begin() RET({*this,Begin(b_)})
LazyT(V,range<const t>&&invocable<const F&,rr_t<const t>>)
CEXP I<1>begin() const RET({*this,Begin(b_)})
AC end() {if CEXP(cm_rg<V>)RET(I<0>{*this,End(b_)})else RET(S<0>{End(b_)})}
LazyT(V,range<const t>&&invocable<const F&,rr_t<const t>>) AC end() const {
if CEXP(cm_rg<V>) return I<1>{*this,End(b_)};
else return S<1>{::end(b_)};
}
LazyT(V,sz_rg<V>) AC size() RET(Size(b_) )
LazyT(V,sz_rg<const V>)AC size() const RET(Size(b_) )
};
TP<CL R,CL F>transform_view(R&&,F)->transform_view<Vw all_t<R>,F>;
Def_Vw_Adp(transform)
TpReq(CL V)(view<V>)
ST take_view:VF<take_view<V>>{
friend VF<take_view<V>>;V b_;rd_t<V>n_;
TP<BL C>CL S:public SF<S<C>>{
friend SF<S<C>>;using SB=s_t<maybe_const<C,V>>;TP<BL D>using CI=counted_iterator<i_t<maybe_const<D,V>>>;SB b_;
BC eq(const CI<C>&i)const RET(i==df||i.base()==b_)
TpReq(BL c=C,CL X=CI<!c>)(s_for<SB,i_t<maybe_const<!c,V>>>)BC eq(const X&i)const RET(i==df||i.base()==b_)
public:S()=default;S(SB s):b_(s){}LazyV(C,C&&conv_to<s_t<V>,SB>)S(S<!C>s):b_(s.b_){}
};
public:take_view(V v,rd_t<V>n):b_(move(v)),n_(n){}
#define B(FL)\
auto begin()FL{if CEXP(sz_rg<FL V>){if CEXP(ra_rg<FL V>)RET(Begin(b_))else RET(counted_iterator(Begin(b_),size()))}else RET(counted_iterator(Begin(b_),n_))}
LazyT(V,!sp_vw<V>)B()LazyT(V,range<const V>)B(const)
#undef B
#define E(FL,X)\
auto end()FL{if CEXP(sz_rg<FL V>){if CEXP(ra_rg<FL V>)RET(Begin(b_)+size())else RET(df)}else RET(S<X>{End(b_)})}
LazyT(V,!sp_vw<V>)E(,0)LazyT(V,range<const V>)E(const,1)
#undef E
#define S(FL) LazyT(V,sz_rg<FL V>)auto size()FL RET(Rg min(Size(b_),(rs_t<FL V>)n_))
S()S(const)
#undef S
};
TP<CL R>take_view(R&&,rd_t<R>)->take_view<Vw all_t<R>>;
Def_Vw_Adp(take)
TpReq(CL V,CL P)(view<V>&&ip_rg<V>&&is_object_v<P>&&ind_up<const P,i_t<V>>)CL take_while_view:public VF<take_while_view<V,P>>{
ST S:SF<S>{
S()=default;S(s_t<V>b,const P*p):b_(move(b)),p_(p){}
private:s_t<V>b_;const P*p_;friend SF<S>;
BC eq(const i_t<V>&i)const RET(i==b_||!invoke(*p_,*i))
};
V b_;box<P>p_;
public:take_while_view(V v,P p):b_(move(v)),p_(move(p)){}
AC begin()RET(Begin(b_))AC end()RET(S{End(b_),&*p_})
};
TP<CL R,CL P>take_while_view(R&&,P)->take_while_view<Vw all_t<R>,P>;
Def_Vw_Adp(take_while)
TpReq(CL V)(view<V>)CL drop_view:public VF<drop_view<V>>{
using D=rd_t<V>;V b_;D n_;c_box<i_t<V>>c_;friend VF<drop_view<V>>;
public:drop_view(V v,D n):b_(move(v)),n_(n){}
AC begin(){if(!c_)c_=Rg next(Begin(b_),n_,End(b_));RET(*c_)}AC end()RET(End(b_))
LazyT(V,sz_rg<const V>)auto size()const RET(::max<rs_t<const V>>(Size(b_)-(rs_t<const V>)n_,0))
LazyT(V,sz_rg<V>)auto size() RET(::max<rs_t<V>>(Size(b_)-(rs_t<V>)n_,0))
};
TP<CL R>drop_view(R&&,rd_t<R>)->drop_view<Vw all_t<R>>;
Def_Vw_Adp(drop)
TpReq(CL V,CL P)(view<V>&&ip_rg<V>&&is_object_v<P>&&ind_up<const P,i_t<V>>)CL drop_while_view:public VF<drop_while_view<V,P>>{
V b_;box<P>p_;c_box<i_t<V>>c_;friend VF<drop_while_view<V,P>>;
public:drop_while_view(V v,P p):b_(move(v)),p_(move(p)){}
AC begin(){if(!c_)c_=Rg find_if_not(b_,cref(*p_));RET(*c_)}AC end()RET(End(b_))
};
TP<CL R,CL P>drop_while_view(R&&,P)->drop_while_view<Vw all_t<R>,P>;
Def_Vw_Adp(drop_while)
//[views.join]
TP<CL R,CL IR=rr_t<R>>concept cjoin=fw_rg<R>&&is_reference_v<IR>&&fw_rg<IR>&&cm_rg<R>&&cm_rg<IR>;
TpReq(CL V)(view<V>&&ip_rg<V>&&ip_rg<rr_t<V>>)CL join_view:public VF<join_view<V>>{
friend VF<join_view<V>>;
TP<BL C>using B=maybe_const<C,V>;TP<BL C>using P=maybe_const<C,join_view>;TP<BL C>using IR=rr_t<B<C>>;
CpBl(Rig,CL X)(is_reference_v<rr_t<X>>);
TP<BL C>SC BL Rig=CpRef(Rig,B<C>);TP<BL C>using D=cm_ty_t<rd_t<B<C>>,rd_t<IR<C>>>;
TP<BL C>using Tg=cd_t<Rig<C>&&bd_rg<B<C>>&&bd_rg<IR<C>>,bd_tag,cd_t<Rig<C>&&fw_rg<B<C>>&&fw_rg<IR<C>>,fw_tag,ip_tag>>;
TP<BL C,CL I>using F=IF<I,Tg<C>,D<C>,rv_t<IR<C>>,rr_t<IR<C>>>;
TP<BL C>CL S;TP<BL C>CL I:public F<C,I<C>>{
TP<BL>friend ST S;TP<BL>friend ST I;friend F<C,I>;
using OI=i_t<B<C>>;using II=i_t<IR<C>>;SC BL Rig=join_view::Rig<C>;using P=P<C>;
OI o_;II i_;P*p_;
VC inc(){auto&&r=[&]()->DCLT(auto){if CEXP(Rig)RET(*o_)else RET(*p_->i_)}();if(++i_==End(r)){++o_;satisfy();}}
LazyT(V,1)VC dec(){if(o_==End(p_->b_))i_=End(*--o_);while(i_==Begin(*o_))i_=End(*--o_);--i_;}
LazyT(V,Rig&&eq_cmp<OI>&&eq_cmp<II>)FC BL eq Crefp(I)RET(i.i_==j.i_&&i.o_==j.o_)
VC satisfy(){
auto g=[this](auto&&x)->auto&&{if CEXP(Rig)RET(*x)else RET(p_->i_.emplace_deref(x))};
for(;o_!=End(p_->b_);++o_){auto&&i=g(o_);i_=Begin(i);if(i_!=End(i))return;}
if CEXP(Rig)i_=II();
}
public:I()=default;CEXP I(P&p,OI o):p_(&p),o_(move(o)){satisfy();}
LazyT(V,C)CEXP I(I<!C>i):o_(move(i.o_)),i_(move(i.i_)),p_(i.p_){}
DCLT(auto) COP*()const RET(*i_)LazyT(V,has_arrow<II>&&copyable<II>)II COP->()const RET(i_)
VC iter_swap Crefp(I)NOEXP_RET(Rg iter_swap(i.i_,j.i_))
CEXP DCLT(auto)iter_move(const I&i)NOEXP_RET(Rg iter_move(i.i_))
};TP<BL C>CL S:public SF<S<C>>{
friend SF<S>;using BS=s_t<B<C>>;BS s_;
public:S()=default;S(P<C>&p):s_(End(p.b_)){}LazyT(V,C&&conv_to<s_t<V>,BS>)S(S<!C>s):s_(s.s_){}
TpReq(BL CC)(s_for<BS,i_t<maybe_const<CC,V>>>)BC eq(const I<CC>&i)const RET(i.o_==s_)
};
V b_;np_box<remove_cv_t<IR<0>>>i_;
public:join_view(V b):b_(move(b)){}
AC begin()RET(I<sp_vw<V>&&Rig<0>>(*this,Begin(b_)))
SC BL cst=ip_rg<B<1>>&&Rig<1>;
LazyT(V,cst)AC begin()const RET(I<1>{*this,Begin(b_)})
AC end(){if CEXP(cjoin<V>)RET(I<sp_vw<V>>{*this,End(b_)})else RET(S<sp_vw<V>>{*this})}
LazyT(V,cst)AC end()const{if CEXP(cjoin<const V>)RET(I<1>{*this,End(b_)})else RET(S<1>{*this})}
};
TP<CL R>join_view(R&&)->join_view<Vw all_t<R>>;
NP views {IC ST join_fn{TP<CL R>auto COP()(R&&r)const NOEXP_DCLT_RET(join_view<Vw all_t<R>>(FWD(r)))} join;}
IC ST search_fn {
TP<CL I,CL S,CL J,CL T,CL Pr,CL P,CL Q>subrange<I>static impl(I a,S b,J x,T y,Pr pr,P p,Q q){
for (;;++a) {I i=a;
for(J j=x;;++i,++j){if(j==y)RET({a,i})if(i==b)RET({i,i})if(!invoke(pr,invoke(p,*i),invoke(q,*j)))break;}
}
}
TpReq(CL R,CL S,CL Pr=equal_to,CL P=idt,CL Q=idt)(fw_rg<R>&&fw_rg<S>&&ind_cmp<i_t<R>,i_t<S>,Pr,P,Q>)
AC operator()(R&&r,S&&s,Pr pr={},P p={},Q q={})const RET(impl(ALL(r),ALL(s),ref(pr),ref(p),ref(q)))
}search;
//[range.split.view]
TpReq(CL V,CL P)(fw_rg<V>&&view<V>&&fw_rg<P>&&view<P>&&ind_cmp<i_t<V>,i_t<P>,equal_to>)
CL split_view:public VF<split_view<V,P>>{
V b_;P p_;friend VF<split_view<V,P>>;
using VI=i_t<V>;using R=subrange<VI>;
R CEXP Nx(VI i){auto[b,e]=Rg search(subrange(i,End(b_)),p_);if(b!=End(b_)&&Rg empty(p_))++b,++e;return{b,e};}
#define Fa IF<I,fw_tag,rd_t<V>,R,R>
CL S;CL I:public Fa{friend Fa;
#undef Fa
split_view*p_;VI i_;R n_;BL t_=0;
VC inc(){i_=n_.begin();if(i_!=End(p_->b_)){i_=n_.end();if(i_==End(p_->b_)){t_=1;n_={i_,i_};}else n_=p_->Nx(i_);} else t_=0;}
FC BL eq Crefp(I)RET(i.i_==j.i_&&i.t_==j.t_)BC rte()const RET(i_==End(p_->b_)&&!t_)
public:I()=default;CEXP I(split_view&p,VI i,R n):p_(&p),i_(i),n_(n){}VI base()const RET(i_)R COP*()const RET({i_,n_.begin()})
};
#define RV rv_t<R>
public:CEXP split_view(V v,P p):b_(move(v)),p_(move(p)){}CEXP split_view(V v,RV p):b_(move(v)),p_(move(Vw single(p))){}
CEXP I begin()RET({*this,Begin(b_),Nx(Begin(b_))})
AC end(){if CEXP(cm_rg<V>)RET(I{*this,End(b_),{}})else RET(df)}
};
TP<CL R,CL P>split_view(R&&,P&&)->split_view<Vw all_t<R>,Vw all_t<P>>;
TP<CL R>split_view(R&&,RV)->split_view<Vw all_t<R>,single_view<RV>>;
Def_Vw_Adp(split)
#undef RV
In_Vws(IC raco counted=[](auto i,id_t<DCLT(i)>k){if CEXP(ra_i<decltype(i)>)RET(subrange{move(i),i+k})else RET(subrange{counted_iterator(move(i),k),df})};)
//[range.reverse.view]
TpReq(CL V)(view<V>&&bd_rg<V>)
CL reverse_view:public VF<reverse_view<V>>{
friend VF<reverse_view<V>>;V b_;c_box<i_t<V>>c_;
public:CEXP explicit reverse_view(V v):b_(move(v)){}
LazyT(V,sz_rg<V>)AC size()RET(Size(b_))
LazyT(V,sz_rg<const V>)AC size()const RET(Size(b_))
AC begin(){if(!c_)c_=Rg next(Begin(b_),End(b_));RET(reverse_iterator(*c_))}AC end()RET(reverse_iterator(Begin(b_)))
};
TP<CL T>reverse_view(T&&)->reverse_view<Vw all_t<T>>;
Def_Vw_Adp(reverse)//first_of [todo]
TP<size_t N>ST has_tp_e{
CpDef(I,CL T)(T t)(Creq(N < tuple_size_v<T>)Cret(conv_to,Rg get<N>(t))(const tuple_element_t<N,T>&));
};
TP<size_t N>ST retable_e {CpBl(I,CL T)(move_cst<tuple_element_t<N,T>>);};
TpReq(CL V,size_t N,CL X=rr_t<V>)(view<V>&&ip_rg<V>&&CpRef(TY has_tp_e<N>::I,rv_t<V>)&&CpRef(TY has_tp_e<N>::I,rmv_r_t<rr_t<V>>)&&
(CpRef(TY retable_e<N>::I,X) || is_reference_v<X>))
CL elements_view:public VF<elements_view<V,N>>{
friend VF<elements_view<V,N>>;
#define B maybe_const<C,V>
#define D rd_t<B>
TP<BL C>using Tg=cd_t<ra_rg<B>,ra_tag,cd_t<bd_rg<B>,bd_tag,cd_t<fw_rg<B>,fw_tag,ip_tag>>>;
#define TE tuple_element_t<N,rv_t<B>>
#define R DCLT(gt(DCLV(i_t<B>)))
#define Fa IF<I<C>,Tg<C>,D,rmv_cvr_t<TE>,R>
TP<CL I>static DCLT(auto)gt(const I&i){if CEXP(is_reference_v<ir_t<I>>)RET(Rg get<N>(*i))else RET(remove_cv_t<tuple_element_t<N,iv_t<I>>>(Rg get<N>(*i)))}
TP<BL C>CL S;TP<BL C>CL I:public Fa{
friend Fa;i_t<B>b_;
public:I()=default;I(i_t<B>b):b_(move(b)){}
R COP*()const RET(gt(b_))
VC inc(){++b_;}LazyT(V,1)VC dec(){--b_;}LazyT(V,1)VC adv(D x){b_+=x;}
LazyT(V,eq_cmp<i_t<B>>)FC BL eq Crefp(I)RET(i.b_==j.b_)LazyT(V,1)FC BL lt Crefp(I)RET(i.b_<j.b_) LazyT(V,1)FC D dif Crefp(I)RET(i.b_-j.b_)
};
V b_;
public:elements_view(V v):b_(move(v)){}
LazyT(V,!sp_vw<V>)AC begin()RET(I<0>{Begin(b_)})
LazyT(V,range<const V>)AC begin()const RET(I<1>{Begin(b_)})
LazyT(V,!sp_vw<V>)AC end(){if CEXP(cm_rg<V>)RET(I<0>{End(b_)})else RET(S<0>{End(b_)})}
LazyT(V,range<const V>)AC end()const {if CEXP(cm_rg<V>)RET(I<1>{End(b_)})else RET(S<1>{End(b_)})}
LazyT(V,sz_rg<V>)AC size()RET(Size(b_))
LazyT(V,sz_rg<const V>)AC size()const RET(Size(b_))
#undef R
#undef B
#undef D
#undef TE
#undef Fa
};
TP<CL T>using key_view=elements_view<T,0>;TP<CL T>using value_view=elements_view<T,1>;
NP views{TP<size_t N>IC auto elements=[](auto&&r)NOEXP_DCLT_RET(elements_view<all_t<DCLT(r)>,N>{FWD(r)});}
In_Vws(CPO keys=elements<0>;CPO values=elements<1>;)
//[range.view.zip]
TP<CL...R>concept czip=(sizeof...(R)==1&&(cm_rg<R>&&...))||(!(bd_rg<R>&&...)&&(cm_rg<R>&&...))||((ra_rg<R>&&sz_rg<R>)&&...);
TP<CL...V>CL zip_view:public VF<zip_view<V...>>{
#define MCV maybe_const<C,V>
#define TMCV(Name) Tp::tp_pa<Name<MCV>...>
#define All_(...) (__VA_ARGS__##_rg<MCV>&&...)
static_assert(sizeof...(V)>0&&((view<V>&&ip_rg<V>) &&...));
tuple<V...>v_;
TP<BL>CL S;
TP<BL C>using Tg=cd_t<All_(ra),ra_tag,cd_t<All_(bd),
bd_tag,cd_t<All_(fw),fw_tag,ip_tag>>>;
TP<BL C>using D=cm_ty_t<rd_t<MCV>...>;
#define F IF<I<C>,Tg<C>,D<C>,TMCV(rv_t),TMCV(rr_t)>
TP<BL C>ST I:F{
TP<BL>friend ST S;friend F;I()=default;CEXP I(TMCV(i_t) i_):i_(move(i_)){}
#undef F
#define CurLazy(...) LazyT(zip_view,__VA_ARGS__)
CurLazy(C&&(conv_to<i_t<V>,i_t<MCV>>&&...))CEXP I(I<!C>i):i_(move(i.i_)){}
auto COP*()const RET(Tp::tran([](auto&i)->DCLT(auto)RET(*i),i_))
void FC iter_move(const I&i)RET(Tp::tran(Rg iter_move,i.i_))
CurLazy((ind_sw<i_t<MCV>>&&...))void FC iter_swap Crefp(I){Tp::for_(Rg iter_swap,i.i_,j.i_);}
private:TMCV(i_t)i_;
VC inc(){Tp::for_([](auto&i){++i;},i_);}CurLazy(1)void dec(){Tp::for_([](auto& i){--i;},i_);}
CurLazy(1)void adv(D<C>n){Tp::for_([n](auto&i){i+=n;},i_);}
CurLazy((eq_cmp<i_t<MCV>>&&...))BL FC eq Crefp(I){if CEXP(All_(bd))RET(i.i_==j.i_)else
RET(apply([](auto...b)RET((b||...)),Tp::tran([](auto&i,auto&j)RET(i==j),i.i_,j.i_)))}
CurLazy(1)BL FC lt Crefp(I)RET(i.i_<j.i_)
CurLazy(1)D<C>FC dif Crefp(I)RET(apply([](auto...b) RET(min(mk_lst({(D<C>)b...}),less{},abs)),Tp::tran([](auto&i,auto&j)RET(i-j),i.i_,j.i_)))
#undef All_
};
TP<BL C>ST S:SF<S<C>>{
friend SF<S<C>>;S()=default;S(TMCV(s_t) s_):s_(move(s_)){}
CurLazy(C&&(conv_to<s_t<V>,s_t<MCV>>&&...))CEXP S(S<!C>i):s_(i.s_){}
private:TMCV(s_t)s_;
#define Def(Name) TpReq(BL CC)((Name##s_for<s_t<MCV>,i_t<maybe_const<CC,V>>>&&...))CEXP
Def()BL eq(const I<CC>&i)const RET(apply([](auto...b) RET((b||...)),Tp::tran([](auto&i,auto&j)RET(i==j),i.i_,s_)))
Def(sz_)auto dif(const I<CC>&i)const
RET(apply([](auto...b)RET(Rg min(mk_lst({(id_t<I<CC>>)b...}),{},Rg abs)),Tp::tran([](auto&i,auto&j)RET(i-j),s_,i.i_)))
#undef Def
};
#undef TMCV
#undef MCV
public:
zip_view(V...v):v_(move(v)...){}
CurLazy(!(sp_vw<V>&&...))CEXP I<0>begin()RET(Tp::tran(Rg begin,v_))
CurLazy((range<const V>&&...))CEXP I<1>begin()const RET(Tp::tran(Rg begin,v_))
CurLazy(!(sp_vw<V>&&...))AC end() {
if CEXP(!czip<V...>)RET(S<0>(Tp::tran(Rg end,v_)))else if CEXP((ra_rg<V>&&...))RET(begin()+size())else RET(I<0>(Tp::tran(Rg end,v_)))
}
CurLazy((range<const V>&&...))AC end()const{
if CEXP(!czip<const V...>)RET(S<0>(Tp::tran(Rg end,v_)))else if CEXP((ra_rg<const V>&&...))RET(begin()+size())else RET(I<0>(Tp::tran(Rg end,v_)))
}
#define SZ(FL) CurLazy((sz_rg<FL V>&&...))AC size() FL \
RET(apply([](auto...a)RET(Rg min(mk_lst({(make_unsigned_t<cm_ty_t<DCLT(a)...>>)a...}))),Tp::tran(Rg size,v_)))
SZ()SZ(const)
#undef SZ
#undef CurLazy
};
TP<CL...R>zip_view(R&&...)->zip_view<Vw all_t<R>...>;
Def_Vw_Adp(zip)
Def_Vw_Adp_(enumerate,[](auto&&...r)NOEXP_DCLT_RET(zip(iota(size_t{0}),FWD(r)...)))//[todo]:iota(0-size)
TpReq(CL V,size_t N)(fw_rg<V>&&view<V>&&(N>0))CL adjacent_view:public VF<adjacent_view<V,N>>{friend VF<adjacent_view>;
#define B maybe_const<C,V>
TP<BL C>using Tg=cd_t<ra_rg<B>,ra_tag,cd_t<bd_rg<B>,bd_tag,fw_tag>>;
#define F IF<I<C>,Tg<C>,rd_t<B>,Tp::repeat<rv_t<B>,N>,Tp::repeat<rr_t<B>,N>>
TP<BL C>CL I:public F{friend F;TP<BL>friend ST I;TP<BL>friend ST S;
using VI=i_t<B>;array<VI,N>i_={};
VC inc(){Tp::for_([](auto&i){++i;},i_);}LazyV(C,1)VC dec(){Tp::for_([](auto&i){++i;},i_);}
LazyV(C,1)VC adv(rd_t<B> n){Tp::for_([n](auto&i){i+=n;},i_);}
FC BL eq Crefp(I)RET(i.i_.back()==j.i_.back())
LazyV(C,1)FC BL lt Crefp(I)RET(i.i_.back()<j.i_.back())
LazyV(C,1)rd_t<B>FC dif Crefp(I)RET(i.i_.back()-j.i_.back())
public:I()=default;CEXP I(B&b){i_[0]=Begin(b);for(size_t i=1;i<N;++i)i_[i]=next(i_[i-1],1,End(b));}
CEXP I(df_t,B&b){if CEXP(bd_rg<B>){i_[N-1]=End(b);for(size_t i=N-1;i--;)i_[i]=prev(i_[i+1],1,Begin(b));}else i_.fill(End(b));}
auto COP*()const RET(Tp::tran([](auto&i)DCLT_RET(*i),i_))
FAC iter_move(const I&i)NOEXP_RET(Tp::tran(Rg iter_move,i.i_))
};
#undef F
TP<BL C>ST S:SF<S<C>>{friend SF<S>;
S()=default;LazyV(C,C&&conv_to<s_t<V>,s_t<B>>)S(S<!C>i):s_(i.s_){}S(B&b):s_(End(b)){}
private:s_t<B>s_;
#define Def(A,R,Na,OP) TpReq(BL CC)(A<s_t<B>,i_t<maybe_const<CC,V>>>)R Na(const I<CC>&i)const RET(i.i_.back()OP s_)
Def(s_for,BL,eq,==)Def(sz_s_for,rd_t<B>,dif,-)
#undef Def
};
#undef B
V b_;
public:adjacent_view(V v):b_(move(v)){}
LazyT(V,!sp_vw<V>)AC begin()RET(I<0>{b_})LazyT(V,range<const V>)AC begin()const RET(I<1>{b_})
LazyT(V,!sp_vw<V>)AC end(){if CEXP(cm_rg<V>)RET(I<0>{df,b_})else RET(S<0>{b_})}
LazyT(V,range<const V>)AC end()const{if CEXP(cm_rg<const V>)RET(I<1>{df,b_})else RET(S<1>{b_})}
#define SZ(FL) LazyT(V,sz_rg<FL V>)auto size() FL {using S=DCLT(Size(b_));using CT=cm_ty_t<S,size_t>;CT r=Size(b_);RET(S(r-::min<CT>(r,N-1)))}
SZ()SZ(const)
#undef SZ
};
NP views{
TP<size_t N>IC auto adjacent=[](auto&&r)NOEXP_DCLT_RET(adjacent_view<all_t<DCLT(r)>,N>{FWD(r)});
IC auto pairwise=adjacent<2>;
}
TP<size_t N,CL T>ST Vi:integral_constant<size_t,N>{
#define D(OP) LazyT(T,ReqExpr(DCLV(const t&)OP DCLV(const t&)))BL FCOP OP Crefp(Vi)RET(i.i OP j.i)
T i;D(==)D(!=)D(<)D(>)D(<=)D(>=)
#undef D
};
TP<CL R>concept can_cm=ra_rg<R>&&sz_rg<R>||cm_rg<R>;
TP<CL...V>concept ccat=can_cm<Tp::back<V...>>;
TP<CL...V>CL concat_view:public VF<concat_view<V...>>{
// ((ip_rg<V>&&view<V>)&&...)
SAC n=sizeof...(V);tuple<V...>v_;
TP<size_t x>auto IEnd()const RET(next(Begin(get<x>(v_)),End(get<x>(v_))))
#define B maybe_const<C,V>
TP<CL...R>using Tg=cd_t<((ra_rg<R>&&sz_rg<R>)&&...),ra_tag,cd_t<((bd_rg<R>&&cm_rg<R>)&&...),bd_tag,cd_t<(fw_rg<R>&&...),fw_tag,ip_tag>>>;
#define D cm_ty_t<rd_t<B>...>
#define VT cm_ty_t<rv_t<B>...>
#define RT cm_ref_t<rr_t<B>...>
#define F IF<I<C>,Tg<B...>,D,VT,RT>
TP<BL C>CL I:public F{friend F;
TP<size_t N,CL T>SAC toI(T t)RET(Vi<N,T>{{},move(t)})
using P=maybe_const<C,concat_view>;
TP<size_t...i>SAC Va(Seq<i...>)->variant<Vi<i,i_t<maybe_const<C,V>>>...>;
using I_=decltype(Va(Tp::idxT<tuple<V...>>{}));
I_ i_;P*p_;
#define K AC k=decay_t<decltype(i)>::value;
AC NxBegin(){visit([&](auto&i){K if CEXP(k+1<n)i_.TP emplace<k+1>(toI<k+1>(Begin(get<k+1>(p_->v_))));},i_);}
AC PrEnd(){visit([&](auto&i){K if CEXP(!!k)i_.TP emplace<k-1>(toI<k-1>(p_->TP IEnd<k-1>()));},i_);}
AC DToBegin()const RET(visit([&](auto&i){K RET(D(i.i-Begin(get<k>(p_->v_))))},i_))
AC DToEnd()const RET(visit([&](auto&i){K RET(D(p_->TP IEnd<k>()-i.i))},i_))
VC sat(){auto f=[&](auto&i){K if CEXP(k==n-1)RET(false)else RET(i.i==End(get<k>(p_->v_)))};while(visit(f,i_))NxBegin();}
VC inc(){visit([](auto&i){++i.i;},i_);sat();}
LazyV(C,1)VC dec(){
auto f=[&](auto&i){K if CEXP(!k)RET(false)else RET(i.i==Begin(get<k>(p_->v_)))};
while(visit(f,i_))PrEnd();
visit([](auto&i){--i.i;},i_);
}
LazyV(C,1)VC adv(D d){
if(d==0)return;
if(d>0){
for(auto w=DToEnd();d>=w;w=DToEnd())d-=w,NxBegin();
visit([d](auto&i){i.i+=d;},i_);
}else{
d=-d;
for(auto w=DToBegin();d>w;w=DToBegin())d-=w,PrEnd();
visit([d](auto&i){i.i-=d;},i_);
}
}
LazyV(C,1)FC D dif Crefp(I){
auto a=i.i_.index(),b=j.i_.index();
auto&h=i.p_->v_;
auto f=[&](auto&x,auto&y)->D{
auto l=x.DToEnd()+y.DToBegin();
l+=Tp::fold(h,x.i_.index()+1,y.i_.index(),plus{},Size);
return l;
};
if(a==b)RET(visit([&](auto&i){K RET(D(i.i-get<k>(j.i_).i))},i.i_))
else if(a<b)RET(-f(i,j))
else RET(f(j,i))
}
LazyT(I_,eq_cmp<I_>)FC BL eq Crefp(I) RET(i.i_==j.i_)LazyV(C,1)FC BL lt Crefp(I) RET(i.i_<j.i_)
BL rte()const RET(i_.index()==n-1&&get<n-1>(i_).i==End(get<n-1>(p_->v_)))
public:I()=default;CEXP I(P&p):p_(&p),i_(in_place_index<0>,toI<0>(Begin(get<0>(p.v_)))){sat();}
CEXP I(P&p,df_t):p_(&p),i_(in_place_index<n-1>,toI<n-1>(p.TP IEnd<n-1>())){}
RT COP*()const RET(visit([](auto&i)DCLT_RET(RT(*i.i)),i_))
#undef J
};
public:CEXP concat_view(V...v):v_(move(v)...){}
LazyV(n,(sp_vw<V>&&...))CEXP I<0>begin()RET({*this})
LazyV(n,(range<const V>&&...))CEXP I<1>begin()const RET({*this})
LazyV(n,(sp_vw<V>&&...))AC end(){if CEXP(ccat<V...>)RET(I<0>{*this,df})else RET(df)}
LazyV(n,(range<const V>&&...))AC end()const {if CEXP(ccat<V...>)RET(I<1>{*this,df})else RET(df)}
#undef B
#undef D
#undef VT
#undef RT
#undef F
#undef K
};
TP<CL...R>concat_view(R&&...)->concat_view<Vw all_t<R&&>...>;
NP views{IC ST concat_fn{TpReq(CL...R)((view<Vw all_t<R>>&&...))AC operator()(R&&...r)const DCLT_RET(concat_view{FWD(r)...});}concat;}
//[views.chunk_by]
TpReq(CL V,CL P)(fw_rg<V>&&is_object_v<P>&&ind_bp<P,i_t<V>,i_t<V>>)CL chunk_by_view:public VF<chunk_by_view<V,P>>{
V b_;box<P>p_;using VI=i_t<V>;friend VF<chunk_by_view<V,P>>;
CEXP VI Nx(VI i)RET(Rg next(Rg adjacent_find(i,End(b_),not_fn(ref(*p_))),1,End(b_)))
LazyT(V,1)CEXP VI Pv(VI i)RET(Rg prev(Rg adjacent_find(reverse_view(subrange(Begin(b_),i)),not_fn(flip(ref(*p_))).base(),1,Begin(b_))))
using R=subrange<VI>;using Tg=cd_t<bd_rg<V>,bd_tag,fw_tag>;
#define F IF<I,Tg,rd_t<V>,R,R>
CL I:public F{
friend F;chunk_by_view*p_;VI i_,n_;
#undef F
VC inc(){i_=n_,n_=p_->Nx(i_);}LazyT(V,1)VC dec(){n_=i_,i_=p_->Pv(n_);}
BL FC eq Crefp(I)RET(i.i_==j.i_)BC rte()const RET(i_==n_)
public:CEXP I()=default;CEXP I(chunk_by_view&p,VI i,VI n):p_(&p),i_(i),n_(n){}
R COP*()const RET({i_,n_})
};
public:chunk_by_view()=default;chunk_by_view(V v,P p):b_(move(v)),p_(move(p)){}
CEXP I begin()RET({*this,Begin(b_),Nx(Begin(b_))})
AC end(){if CEXP(cm_rg<V>)RET(I{*this,End(b_),End(b_)})else RET(df)}
};
TP<CL R,CL P>chunk_by_view(R&&,P)->chunk_by_view<Vw all_t<R>,P>;

Def_Vw_Adp(chunk_by)
//[view.subset]
TP<CL T>CL subset_view:public VF<subset_view<T>>{
#define Fa IF<I,fw_tag,id_t<T>,T,T>
CL I:public Fa{
friend Fa;T t,v_;
VC inc()noexcept{v_=(v_-1)&t;}
BL FC eq Crefp(I)noexcept RET(i.v_==j.v_)BC rte()const noexcept RET(v_==t)
public:I()=default;CEXP I(T t)noexcept:t(t),v_(t&(t-1)){}
T COP*() const noexcept RET(v_)
};
T t;
public:CEXP subset_view(T t) noexcept:t(t){}
CEXP I begin()const noexcept RET( { t } )CEXP df_t end()const noexcept RET({})
AC size()const noexcept RET( to_unsigned(T{1})  << __popcount(t) )
};
Def_Vw_Adp(subset)
TP<CL T>CL decompose_view:public VF<decompose_view<T>>{
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
TP<TPP C,CL R,CL...A>using Cont=DCLT(C(proxy_iter<R>(),proxy_iter<R>(),DCLV(A)...));
TP<CL C>struct to_{
TP<CL E>SAC get=first_of(
[](C&c)NOEXP_DCLT_RET((void)ReqExpr(c.push_back(DCLV(E))),back_inserter(c)),
[](C&c)NOEXP_DCLT_RET((void)ReqExpr(c.insert(end(c),DCLV(E))),inserter(c,end(c)))
);
SAC impl=first_of(
[](auto&&r,auto&&...a)NOEXP_DCLT_RET(C(FWD(r),FWD(a)...)),
[](auto&&r,auto&&...a)NOEXP_DCLT_RET(C(begin(r),end(r),FWD(a)...)),
[](auto&&r,auto&&...a)NOEXP_DCLT((void)ReqExpr(get<rr_t<DCLT(r)>>(DCLV(C&))),C{})
{using R=DCLT(r);auto c=C(FWD(a)...);if CEXP(sz_rg<R>)if CEXP(can_reserve<C>)c.reserve(size(r));Rg copy(r,get<rr_t<R>>(c));return c;}
);
SC raco fn=impl;
};
TP<TPP C>ST toT{TP<CL R,CL...A>auto COP()(R&&r,A&&...a)const NOEXP_DCLT_RET(to_<Cont<C,R,A...>>::impl(FWD(r),FWD(a)...))};
TP<CL C,CL...A>AC to(A&&...a)DCLT_RET(to_<C>::fn(FWD(a)...))
TP<TPP C,CL...A>AC to(A&&...a)DCLT_RET(raco(toT<C>{})(FWD(a)...))
TpReq(CL V)(view<V>&&bd_rg<V>)CL combination_view:public VF<combination_view<V>>{
using S=combination_view;
friend VF<S>;using VI=i_t<V>;using D=rd_t<V>;
V b_;vector<VI>c_;D n_;CL I;
using F=IF<I,ip_tag,D,rv_t<V>,rr_t<V>>;
ST I:F{friend F;
I()=default;I(S&p):p_(&p){}I(I&&)=default;I&operator=(I&&)=default;
auto COP*()const RET(p_->c_|Vw transform([](auto&&x)DCLT_RET(*x)))
private:S*p_;VC inc(){p_->Nx();}BC rte()const RET(p_->rte())
};
VC Nx(){
if(!n_)RET(void(n_=-1));auto i=c_.rbegin();
for(auto j=prev(next(Begin(b_),End(b_)));i!=c_.rend()&&*i==j;++i,--j);
if(i!=c_.rend())iota(next(i).base(),c_.end(),++*i);else ++c_.back();
}
BC rte() RET(n_==-1||!empty(c_)&&c_.back()==End(b_))
public:combination_view(V v,D n):b_(move(v)),n_(n){}
AC begin(){c_=Vw iota(Begin(b_),Begin(b_)+n_)|to<vector>();RET(I{*this})}
AC end()RET(df)
LazyT(V,sz_rg<V>)AC size(){if(n_<=0)RET(1)using U=rs_t<V>;RET((U)basic_mod<U{0}-1>::comb(Size(b_),n_))}
};
TP<CL R>combination_view(R&&,rd_t<R>)->combination_view<Vw all_t<R>>;
Def_Vw_Adp(combination)

TP<TPP X,CL V,CL I>ST counter_{
TpReq(CL R,CL P=idt,CL...A)(Rg range<R>&&(is_void_v<V>||conv_to<ind_res_t<P,i_t<R>>,V>))auto operator()(R&&r,P p={},A&&...a)const{
auto x=[&]{if CEXP (is_void_v<V>)return X<rmv_cvr_t<ind_res_t<P,i_t<R>>>,I>(FWD(a)...);else return X<V,I>(FWD(a)...);}();
for(auto&&r:FWD(r))++x[invoke(p,FWD(r))];RET(x)
}
};
TP<TPP X=unordered_map,CL V=void,CL I=ptrdiff_t>inline constexpr raco counter=counter_<X,V,I>{};
inline constexpr raco slide = [](auto&&r,size_t len) {
    auto f=begin(r);auto l=end(r);
    return Vw iota(f,max(f,l-len+1))|views::transform([=](auto i)RET(i|views::counted(len)));
};
}//ranges
TP<CL L,CL R>AC operator+(L&&l,R&&r)DCLT_RET(Rg Vw concat(FWD(l),FWD(r)))
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
TP<CL S>void impl(S&,const string&,tag<6>)=delete;
TP<CL S,size_t N>void impl(S&,const char(&)[N],tag<6>)=delete;
TP<CL S,TPP W,CL R,CL...Re,CL=Req(Rg range<R>),CL=void_t<TY W<R,Re...>::fmt>>void impl(S&s,W<R,Re...>,tag<3>);
TP<CL S,TPP W,CL T,CL...Re,CL=TY tuple_size<rmv_cvr_t<T>>::type,CL=void_t<TY W<T,Re...>::fmt>>
void impl(S&,W<T,Re...>w,tag<2>);
TP<CL S,CL R,CL=Req(Rg range<R>)>void impl(S&s,R&&r,tag<1>);
TP<CL S,CL T,CL=TY tuple_size<rmv_cvr_t<T>>::type>void impl(S&s,T&&t,tag<0>);
//op
TP<CL Ch,CL Tr,CL T>auto operator<<(basic_ostream<Ch,Tr>&s,T&&t)DCLT_RET(impl(s,t,tag<6>{}),s)
//impl
#define DEF auto d=[&]{if CEXP(has_del<WW>)return w.d;else return default_delim;};auto b=[&]{if CEXP(has_bra<WW>)return w.b;else return default_brac;};
#define MSeq make_Seq<tuple_size_v<rmv_cvr_t<T>>>{}
TP<CL S,CL T,CL B,CL D,size_t...I>
void T_impl(S&s,T&&t,Seq<I...>,B b,D d){Raii _{s,b};((put_delim(s,I==0,d)<<fmt(get<I>(FWD(t)))),...);}
TP<CL S,CL R,CL B,CL D>void R_impl(S&s,R&&r,B b,D d){Raii _{s,b};size_t i=0;for(auto&&e:r)put_delim(s,++i==1,d)<<fmt(e);}
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
TP<CL...T>using limits=numeric_limits<cm_ty_t<T...>>;
TP<CL TT,CL UU>IC BL eq(TT&&t,UU&&u){DEF
if CEXP(is_integral_v<T>&&is_integral_v<U>)
{if CEXP(is_signed_v<T> ==is_signed_v<U>)RET(t==u)else if CEXP(is_signed_v<T>)RET(t<0?0:to_unsigned(t)==u)else RET(u<0?0:t==to_unsigned(u))}
else if CEXP(is_floating_point_v<U>||is_floating_point_v<T>){auto x=abs(t-u);return x<=limits<T,U>::epsilon()*ulp || x<limits<T,U>::min();}
else RET(t==u)
}
TP<CL TT,CL UU>IC BL lt(TT&&t,UU&&u){DEF
if CEXP(is_integral_v<T>&&is_integral_v<U>)
{ if CEXP(is_signed_v<T> ==is_signed_v<U>)RET(t<u)else if CEXP(is_signed_v<T>)RET(t<0?1:to_unsigned(t)<u)else RET(u<0?0:t<to_unsigned(u))}
else if CEXP(is_floating_point_v<T>||is_floating_point_v<U>)RET(eq(t,u)?0:t<u)
else return t<u;
}
#undef DEF
TP<CL T>CL sf{ 
T v={};
public:
sf()=default;TP<CL U>CEXP sf(U&&x):v(FWD(x)){}
COP T() const { return v;}
};
TP<CL T>sf(T)->sf<T>;inline sf<ull>COP ""_sf(ull x) { return x;}
inline sf<long double>COP ""_sf(long double x) { return x;}

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
inline NP unionfind {
CL UF {
vector<int>fa,sz;
size_t n,comp_cnt;
public:
UF(size_t n):n(n),comp_cnt(n),fa(n),sz(n,1) {
iota(begin(fa),end(fa),0);
}
auto size() { return n;}
auto count() { return comp_cnt;}
int findset(int x) { return fa[x]==x ? x:fa[x]=findset(fa[x]);}
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
CpDef(can_top,CL T)(T&t)(t.top(),);
AC pop=[](auto&t){
using T=decay_t<DCLT(t)>;auto r=move((TY T::value_type&)[&]()->auto&&{if CEXP(CpRef(can_top,T))RET(t.top())else RET(t.front())}());
t.pop();return r;
};
}//utility
inline NP direction {
CEXP int dir [][2]{{0,1},{1,0},{0,-1},{-1,0}};
CEXP int dir8[][2]{{0,1},{1,0},{0,-1},{-1,0},{1,1},{-1,1},{1,-1},{-1,-1}};
AC valid=[](auto m,auto n)RET([=](size_t x,size_t y)RET(x<m&&y<n));
}
#ifdef __cpp_lib_memory_resource
IC auto set_pmr=[]{static byte buf[1<<30];static auto pool=pmr::monotonic_buffer_resource{data(buf),size(buf)};set_default_resource(&pool);RET(0)};
#endif
IC auto set_fast_io=[]{ios::sync_with_stdio(0);cin.tie(0);cout.tie(0);cout << setprecision(12);return 0;};
#define Tpsn(Xarg) Tps(Pack(CL...A),Xarg##_view<A...>)
Tpsn(ref)Tpsn(take)Tpsn(drop)Tpsn(join)Tpsn(reverse)
Tpsn(filter)Tpsn(transform)Tpsn(take_while)Tpsn(drop_while)Tpsn(split)
Tpsn(concat)Tpsn(zip)
#define Tps1N(Xarg) Tps(Pack(CL A,size_t N),Xarg##_view<A,N>)
Tps1N(elements)Tps1N(adjacent)
#undef Tps1N
#undef Tpsn
#undef Tps
NP views=Rg views;
using Vw single,Vw filter,Vw take,Vw take_while,Vw drop,Vw drop_while,Vw join,Vw split,Vw elements,Vw keys,Vw values;
CPO Distance=Rg distance;
CPO Min=Rg min;CPO Max=Rg max;
}//std
inline NP simplify{
CPO tran=Vw transform;
CPO range=Vw iota;CPO All=Vw all;CPO fac=Vw decompose;CPO Enum=Vw enumerate;CPO rev=Vw reverse;
using Vw subset,Vw chunk_by,Vw zip,Rg counter,Rg to,Rg subrange,Rg fold,Vw combination,Vw concat,Vw adjacent, Vw pairwise;
TP<size_t N>IC auto First=views::adjacent<N>^[](auto&&r)DCLT_RET(r.front());
TP<size_t N>IC auto RFirst=views::transform(First<N>);
TP<size_t N>IC auto flat_map=[](auto&&f)RET(views::transform(FWD(f))^views::join);

IC auto iters=[](auto&&r)RET(range(ALL(r)));
#define L(...) [&](auto&&_)RET(__VA_ARGS__)
#define L2(...) [&](auto&&_1,auto&&_2)RET(__VA_ARGS__)
}
