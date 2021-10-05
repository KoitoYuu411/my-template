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

//[Min]
vector<string> nums={"3","2","45","13","100"};
//different Min
debug(Min(nums))
debug(Min(nums,greater{}))
debug(Min(nums,less{},Size))
debug(Min(nums,less{},[](auto x)RET(make_pair(Size(x),ref(x)))))
//mix-types
long x=2;unsigned y=4;
debug(Min(x,y)) //Returns long(2)
//Bind operator
auto z=y|Min(x,less{},[&](auto&&i)RET(nums[i])); // equals to Min(y,x,less{},Lambda) Use nums[i] as key
debug(z)
y|=Min(x);//equals to y=y|Min(x) -> y=Min(y,x)
debug(y)

  
  
  
