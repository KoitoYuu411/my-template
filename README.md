# my-template
# ranges
Rg XXX means ranges::XXX
## algorithms
### Rg min
#### demo
```cpp
vector<string> nums={"3","2","45","13","100"};
//different Min
Min(nums)// "100"
Min(nums,greater{}) //"45"
Min(nums,less{},Size)//"3"
Min(nums,less{},[](auto&&x)RET(make_pair(Size(x),ref(x))))//"2"
//mix-types
long x=2;unsigned y=4;
Min(x,y) //Returns long(2)
//Bind operator
auto z=y|Min(x,less{},[&](auto&&i)RET(nums[i])); // equals to Min(y,x,less{},Lambda) Use nums[i] as key
y|=Min(x);//equals to y=y|Min(x) -> y=Min(y,x)
```

### Rg fold
#### demo
```cpp
vector x={1.0,-3.0,4.4};
debug(x|Rg fold(0)) // returns 2.4
debug(x|Rg fold(0,{},Rg abs)); //return 8.4
debug(x|Rg fold(1,multiplies{})); //return -13.2
```
## to
```
set_pmr();
using A=pmr::polymorphic_allocator<int>;
auto c = 676|fac|to<vector>(A{});
static_assert(is_same_v<decltype(c),pmr::vector<int>>);
return {};
```

Vw XXX means views::XXX
## views

## Macros
### ConceptDef
```cpp
TP<CL T>concept swappable=ConceptRef(swappable,T);
ConceptDef(swappable_with,CL T,CL U)(T&& t,U&& u) (
Reqs(common_reference_with<T,U>) // requirement
my_swap(FWD(t),FWD(t)),         // expression
);
```
is equivalent to 
```cpp
template<class T>
concept swappable = requires(T&& t, U&& u) {
    requires common_reference_with<T,U>;
    my_swap(std::forward<T>(t), std::forward<U>(u);
};
```



```
template<class In>
  concept indirectly-readable-impl =
    requires(const In in) {
      typename iter_value_t<In>;
      typename iter_reference_t<In>;
      typename iter_rvalue_reference_t<In>;
      { *in } -> same_­as<iter_reference_t<In>>;
      { ranges::iter_move(in) } -> same_­as<iter_rvalue_reference_t<In>>;
    } &&
    common_­reference_­with<iter_reference_t<In>&&, iter_value_t<In>&> &&
    common_­reference_­with<iter_reference_t<In>&&, iter_rvalue_reference_t<In>&&> &&
    common_­reference_­with<iter_rvalue_reference_t<In>&&, const iter_value_t<In>&>;
template<class In>
  concept indirectly_­readable =
    indirectly-readable-impl<remove_cvref_t<In>>;
```
