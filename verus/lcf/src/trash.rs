//DAFNY Code
  /* function merge_subst(s : Subst, t : Subst) : (res : Result<Subst>)
   ensures res.Ok? ==> (
              && compatible_subst(s, t)
              && res.val.Keys == s.Keys + t.Keys
              && (forall v :: v in s ==> res.val[v] == s[v])
              && (forall v :: v in t ==> res.val[v] == t[v])
            )
  {
    if compatible_subst(s, t) then Ok(s+t) else Err
  } 
  */

  //putting on hold temporarily
  /* fn merge_subst(s : Subst, t : Subst) -> (res: Result<Subst, ()>)
    /* ensures res.is_Ok() ==> (
              compatible_subst(s, t),
              res.val.Keys == s.Keys + t.Keys,            //clean up code
              (forall |v : Const| res.val[v] == s[v]),
              (forall |v : Const| res.val[v] == t[v]),
    ) */
  {
    if compatible_subst(s, t){
      let mut u = StringHashMap::<Const>::new();
      //need to find method to iterate through s and t
      for (key, val) in s.iter() {
        u.insert(key, val);
      }
      for (key, val) in t.iter() {
        u.insert(key, val);
      } 
       Ok(s + t)  // figure out 
       // update do iteration and add all key-value pairs into single hashmap and run Ok
       //on the joint set
      
    }
    else 
    {
      Err(())
    }
  }  */