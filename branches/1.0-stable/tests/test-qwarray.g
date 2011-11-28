Include "../lib/uwarray.g".
Include "../lib/qwarray.g".

Set "no_expand_vars"

Define T := <uwarray word 0x4>
Define g := fun(u:Unit):#unique T. (uwarray_new word 0x4 0x0).

Define main :=
  let arr = (qwarray_new T 0x10 g)
  
  % testing "get"
  let iarr = (inspect_unique <qwarray T 0x10> arr)
  cabbrev p = join (ltword 0x0 0x10) tt
  let x = (qwarray_get T 0x10 iarr 0x0 p)
  do
  (consume_unique_owned T x)
  (consume_unique_owned <qwarray T 0x10> iarr)
  
  % testing "set"
  let x1 = (uwarray_new word 0x4 0x1)
  let arr = (qwarray_set T 0x10 arr 0x0 x1 p)
  
  % testing "swap"
  let x2 = (uwarray_new word 0x4 0x1)
  let arr =
		match (qwarray_swap T 0x10 arr 0x0 x2 p) with qwarray_swap_v _ x3 n' arr =>
		do
		% free to access x3
		(uwarray_free word 0x4 x3)
		cast arr by cong <qwarray T *> join n' 0x10
		end
	  end	% match

	% testing "free"  
  (qwarray_free T 0x10 arr)
  end	% do

%Set "debug_eta_expand".
%Set "debug_to_carraway".
%Set "debug_stages".

Compile main to "test-qwarray.c".
