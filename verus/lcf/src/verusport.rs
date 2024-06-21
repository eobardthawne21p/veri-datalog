

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
use vstd::seq::Seq;


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

pub enum Const {
  Atom (String),
  Nat (u64), 
  Str (String),
  List (Vec<Const>) // vector???
  } 

/* pub enum SpecConst {
  Atom (String),
  Nat (u64), 
  Str (String),
  List (Seq<SpecConst>)
  } */

/* impl DeepView for Const {
  type V = SpecConst;

  open spec fn deep_view(&self) -> Self::V {
    match self {
      Const::Atom(s) => SpecConst::Atom(*s),
      Const::Nat(n) => SpecConst::Nat(*n),
      Const::Str(s) => SpecConst::Str(*s),
      Const::List(vec) => SpecConst::List(vec.deep_view()),
        
        /* let mut seq = Seq::<SpecConst>::empty();
        for i in 0..vec.len() {
            seq = seq.push(vec[i as int].deep_view());
        }

        SpecConst::List(seq) */
    
      
    }
  }
} */
  
  

  fn main(){

  }
}

    



