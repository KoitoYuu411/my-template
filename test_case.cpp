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
