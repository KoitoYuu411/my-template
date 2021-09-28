# my-template

## ConceptDef
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
