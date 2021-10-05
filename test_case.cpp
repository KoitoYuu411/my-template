#define IS_SAME(...) static_assert(same_as<__VA_ARGS__>);
//[indirectly_readable_traits]
struct X{using value_type = int; using element_type=int;};
struct Y{using value_type = int; using element_type=float;};
IS_SAME(TY indirectly_readable_traits<int[3]>::value_type, int)
IS_SAME(TY indirectly_readable_traits<shared_ptr<int>>::value_type, int)
IS_SAME(TY indirectly_readable_traits<const int*>::value_type, int)
IS_SAME(TY indirectly_readable_traits<const int*const >::value_type, int)
IS_SAME(TY indirectly_readable_traits<X>::value_type, int)
IS_SAME(TY indirectly_readable_traits<vector<int>::iterator>::value_type, int)
IS_SAME(TY indirectly_readable_traits<Y>::value_type, int)//failed

  
//[indirectly_readable]
static_assert(indirectly_readable<shared_ptr<int>>);
static_assert(indirectly_readable<int const*const>);
static_assert(indirectly_readable<vector<bool>::iterator>);
// static_assert(indirectly_readable<optional<int>>); // fail



//[pipeline]
raco max = [](auto&&a,auto&&b)RET(std::max(FWD(a),FWD(b)));
auto l = vector {1,2,3} |= tran < raco(minus{}) % 3 | to<vector>();
auto ret = INT_MIN;
for (auto x : l) ret |= max(x);
debug(ret)
  
  
  
