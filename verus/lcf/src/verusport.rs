use vstd::prelude::*;
use crate::string_hash_map::StringHashMap;
use vstd::seq::Seq;
use vstd::std_specs::result;



verus! {



  // enum Const declaration
  pub enum Const {
    Atom (String),
    Nat (u64), 
    Str (String),
    //List (Vec<Const>), // vector???
    } 

impl Const {
  fn clone (&self) -> (res: Self)
    ensures self == res
    {
    
      match self {
        Const::Atom(s) => Const::Atom(s.clone()),
        Const::Nat(n) =>  Const::Nat(*n),
        Const::Str(s) =>  Const::Str(s.clone()),
      }
   }
}
/*pub enum SpecConst {
  Atom (String),
  Nat (u64),            // waiting on conversion from vec to seq issue to be resolved
  Str (String),
  //List (Seq<SpecConst>)
  } */

/* impl DeepView for Const {    // attmept at forcing vec units into seq
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

  // Subst using StringHashMap from string_hash_map crate
  type Subst = StringHashMap<Const>;
  


// spec fn in place of predicate for compatible substitution
  spec fn compatible_subst(s : Subst, t : Subst) -> bool
  {
    forall|v: String| (#[trigger] s@[v@]) == (#[trigger] t@[v@])
  }

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

 //Verus code for Term
 // enumeration of data types in type Term (Const and Strings)
 pub enum Term {
  Const (Const),
  Var(String),
 }
 
 impl Term {
 // clone fn to be used in operations later
 fn clone (&self) -> (res: Self)
 ensures self == res
 {
   match self {
     Term::Var(s) => Term::Var(s.clone()),
     Term::Const(c) => Term::Const(c.clone()) ,
   }
}
//predicate complete_subst rewritten as a spec fn that returns bool
  pub open spec fn complete_subst(self, s: Subst) -> bool
  {
    match self {
      Term::Var(v) => s@.contains_key(v@), //look for hashmap function v in s or key in map
      Term::Const(_) => true,
    }
  } 
  //predicate concrete rewritten as a spec fn that returns bool
  pub open spec fn concrete(self) -> bool
  {
    self is Const
    // match self {
    //   Term::Const(_) => true,
    //   _ => false,
    // }
      //find function for Const?
  } 

 //exec fn subst
 fn subst(self, s: &Subst) -> (res: Term)
  requires self.complete_subst(*s)
  ensures res.concrete()
 {
  match self{
      //Term::Var(v) => Term::Const(s@[v@]),
      Term::Var(v) => {
        let u_option = s.get(v.as_str());
        Term::Const(u_option.unwrap().clone())
        /* if let Some(u) = s.get(v.as_str()){
        Term::Const(*u)
        }
        else{

        } */
      },
      Term::Const(_) => self,
  }
  } 

 }

pub enum Prop {
  App(String, Vec<Term>),
  Eq(Term, Term),
  //BuiltinOp(b: Builtin, args: Vec<Term>),
  // will add in BuiltinOp when Builtin is implemented
}
impl Prop {

  pub open spec fn complete_subst(self, s: &Subst) -> bool
  {
    match self {
      Prop::App(head, args) => forall|i : int| #![auto] 0 <= i < args.len() ==> args[i].complete_subst(*s),
      Prop::Eq(x, y) => x.complete_subst(*s) && y.complete_subst(*s)
      //Prop::BuiltinOp(_, args) => forall| i : Subst| 0 <= i as i32 < args.len() ==> args[i as i32].complete_subst(),
    }
  }
  pub open spec fn concrete(self) -> bool {
    match self {
    Prop::App(head, args) => forall| i : int| #![auto] 0 <= i < args.len() ==> args[i].concrete(),
    Prop::Eq(x, y) => x.concrete() && y.concrete(),
    //Prop::BuiltinOp(_, args) => forall| i : int| 0 <= i < args.len() ==> args[i].concrete()
    }
  }

  fn subst(&self, s: &Subst) -> (res: Prop)
  requires self.complete_subst(s)
  ensures res.concrete(),
  {
  match self
  {
    Prop::App(h, args) => {
      let mut v = Vec::<Term>::new();
      for i in 0..args.len()
      invariant 0 <= i <= args.len(),
                v.len() == i,
                forall |j: int| #![auto] 0 <= j < args.len() ==> args[j].complete_subst(*s),
                forall |j: int| #![auto] 0 <= j < i ==> v[j].concrete()
      {
        v.push(args[i].clone().subst(s));
      }
      Prop::App(h.clone(), v)
    }
    Prop::Eq(x, y) => Prop::Eq(x.clone().subst(s), y.clone().subst(s))
  }
}

  pub open spec fn symbolic(self) -> bool
  {
    self is App
  }

  spec fn valid(self) -> bool 
  {
    if self.symbolic() == true
    {
      false
    }
    else if self.concrete() == false
    {
      false
    }
    else 
    {
      match self {
        Prop::Eq(x, y) => match (x,y) {
          (Term::Const(x), Term::Const(y)) => if x == y {
            true
          }
          else
          {
            false
          },
          (Term::Var(x), Term::Var(y)) => false,
          (Term::Const(_), Term::Var(_)) | (Term::Var(_), Term::Const(_)) => false,

        }
        Prop::App(s, v) => false,
        /* Prop::BuiltinOp(b, args) => (
          // will implement when we do buitlins
        ) */
      }
    }
  } 
}

pub struct Rule {
  pub head : Prop,
  pub body : Vec<Prop>,
  pub id : u64,
}

impl Rule {
  pub open spec fn complete_subst(self, s: &Subst) -> bool {
    self.head.complete_subst(s) && forall| i : int| #![auto] 0 <= i < self.body.len() ==> self.body[i].complete_subst(s)
  }

  pub open spec fn concrete(self) -> bool {
    self.head.concrete() && forall| i : int| #![auto] 0 <= i < self.body.len() ==> self.body[i].concrete()
  }

  fn subst(&self, s : &Subst) -> (res : Rule) 
  requires self.complete_subst(s)
  ensures res.concrete()
  {
    let mut v = Vec::<Prop>::new();
    for i in 0..self.body.len()
    invariant 0 <= i <= self.body.len(),
    v.len() == i,
      forall |j: int| #![auto] 0 <= j < self.body.len() ==> self.body[j].complete_subst(s),
      forall |j: int| #![auto] 0 <= j < i ==> v[j].concrete()
    {
      v.push(self.body[i].subst(s));
    }
    let result = Rule {
      head : self.head.subst(s),
      body : v,
      id : self.id,
    };
    result
  } 

 pub open spec fn wf(self) -> bool {
  self.head.symbolic()
 }
}


fn main(){
    
}

}  

    



