

/* datatype Result<A> = Ok(val : A) | Err {
  predicate IsFailure() { this.Err? }
  fn PropagateFailure() : Result<A>
    requires IsFailure() {
    Err
  }
  fn Extract() : A
    requires !IsFailure() {
    val
  }
} */



//#[allow(inconsistent_fields)]
//use vstd::std_specs::result;
use vstd::prelude::*;
use crate::string_hash_map::StringHashMap;

verus! {

/* enum Result<A> {
    Ok { val: A },
    Err,
}

impl<A> Result<A> {
    
    spec fn IsFailure(&self) -> bool {
        matches!(self, Result::Err {err})
    }

    
    fn PropagateFailure(&self) -> Result<A> 
        requires self.IsFailure()
    {
        Result::Err 
    }

    
    fn Extract(&self) -> &A 
        requires !self.IsFailure()
    {
      match self {
        Result::Ok { val } => val,
        Result::Err => Err,
    } 
    }
  } */

  enum Const {
    Atom { val : String },
    Nat { i : u16 }, 
    Str { s : String },
    List { l : Vec<Const>} // vector???
  }
  

  // fn main(){

  // }
}

    



