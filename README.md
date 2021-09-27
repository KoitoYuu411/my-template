# my-template

# ConceptDef
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
