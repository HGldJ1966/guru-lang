Include "../lib/uwarray.g".

Define test :=
  let a = (uwarray_new word word8 word0) in
  let a = (uwarray_set word word3 word1 word8 a join (lt (to_nat word3) (to_nat word8)) tt) in
    (uwarray_free word word8 a).

Compile test to "test-uwarray.c".
