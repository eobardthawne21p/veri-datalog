use vstd::prelude::*;
use crate::string_hash_map::StringHashMap;
use vstd::seq::Seq;
use vstd::std_specs::result;

verus! {

  pub enum Const {
    Atom (String),
    Nat (u64), 
    Str (String),
    //List (Vec<Const>), // vector???
  } 

  impl PartialEq for Const {
    fn eq(&self, other : &Self) -> (res: bool)
      ensures res <==> self.deep_view() == other.deep_view()
    {
      match (self, other) {
      (Const::Atom(s), Const::Atom(t)) => s == t,
      (Const::Nat(u), Const::Nat(v)) => u == v,
      (Const::Str(s), Const::Str(t)) => s == t,

      (Const::Atom(_), Const::Nat(_)) | (Const::Nat(_), Const::Atom(_)) => false,
      (Const::Atom(_), Const::Str(_)) | (Const::Str(_), Const::Atom(_)) => false,
      (Const::Str(_), Const::Nat(_)) |  (Const::Nat(_), Const::Str(_)) => false,


      }
    }
  }

  impl Clone for Const {
    fn clone(&self) -> (res: Self) 
      ensures self.deep_view() == res.deep_view()
    { 
      match self {
        Const::Atom(s) => Const::Atom(s.clone()),
        Const::Nat(n) =>  Const::Nat(*n),
        Const::Str(s) =>  Const::Str(s.clone()),
      }
    }
  }

  impl Const {
  /* fn clone (&self) -> (res: Self)
    ensures self == res
    {
    
      match self {
        Const::Atom(s) => Const::Atom(s.clone()),
        Const::Nat(n) =>  Const::Nat(*n),
        Const::Str(s) =>  Const::Str(s.clone()),
      }
   } */
  }
pub enum SpecConst {
  Atom (String),
  Nat (u64),            // waiting on conversion from vec to seq issue to be resolved
  Str (String),
  //List (Seq<SpecConst>)
  }

impl DeepView for Const {    // attempt at forcing vec units into seq
  type V = SpecConst;

  open spec fn deep_view(&self) -> Self::V {
    match self {
      Const::Atom(s) => SpecConst::Atom(*s), 
      Const::Nat(n) => SpecConst::Nat(*n),
      Const::Str(s) => SpecConst::Str(*s),
      // Const::List(vec) => SpecConst::List(vec.deep_view()),
        
        /* let mut seq = Seq::<SpecConst>::empty();
        for i in 0..vec.len() {
            seq = seq.push(vec[i as int].deep_view());
        }

        SpecConst::List(seq) */
    
      
    }
  }
}

  
  type Subst = StringHashMap<Const>;
  type SpecSubst = Map<Seq<char>, SpecConst>;


  spec fn compatible_subst(s : Subst, t : Subst) -> bool
  {
    forall|v: String| (#[trigger] s.deep_view()[v@]) == (#[trigger] t.deep_view()[v@])
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

  pub enum Term {
    Const (Const),
    Var(String),
  }

  pub enum SpecTerm {
    Const (SpecConst),
    Var(Seq<char>),
  }

  impl DeepView for Term {
    type V = SpecTerm;

    open spec fn deep_view(&self) -> Self::V {
      match self {
        Term::Const(c) => SpecTerm::Const(c.deep_view()),
        Term::Var(s) => SpecTerm::Var(s.view()),
      }
    }
  }

  impl Clone for Term {
    fn clone(&self) -> (res: Self) 
    ensures self.deep_view() == res.deep_view()
    { 
      match self {
        Term::Var(s) => Term::Var(s.clone()),
        Term::Const(c) => Term::Const(c.clone()) ,
      }
    }
  }

  impl PartialEq for Term {
    fn eq(&self, other : &Self) -> (res: bool)
      ensures res <==> self.deep_view() == other.deep_view()
    {
      match (self, other) {
        (Term::Const(c), Term::Const(d)) => c == d,
        (Term::Var(s), Term::Var(t)) => s == t,

        (Term::Const(_), Term::Var(_)) | (Term::Var(_), Term::Const(_)) => false,
      }
    }
  }
 
  impl Term {
  
    pub open spec fn complete_subst(self, s: Subst) -> bool
    {
      match self {
        Term::Var(v) => s@.contains_key(v@), 
        Term::Const(_) => true,
      }
    } 
  
    pub open spec fn concrete(self) -> bool
    {
      self is Const
    } 

    pub fn subst(self, s: &Subst) -> (res: Term)
    requires self.complete_subst(*s)
    ensures res.concrete()
    {
      match self {
        Term::Var(v) => {
          let u_option = s.get(v.as_str());
          Term::Const(u_option.unwrap().clone())
        },
        Term::Const(_) => self,
      }
    } 

    /* pub open spec fn SpecSubst(self, s: &Subst) -> (res: Term)
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
    } */

  }

  pub enum Prop {
    App(String, Vec<Term>),
    Eq(Term, Term),
    //BuiltinOp(b: Builtin, args: Vec<Term>),
    // will add in BuiltinOp when Builtin is implemented
  }

  pub enum SpecProp {
    App(Seq<char>, Seq<SpecTerm>),
    Eq(SpecTerm, SpecTerm),
  }

  impl DeepView for Prop {
    type V = SpecProp;

    open spec fn deep_view(&self) -> Self::V {
      match self {
        Prop::App(s, v) => SpecProp::App(s.view(), v.deep_view()),
        Prop::Eq(t, e) => SpecProp::Eq(t.deep_view(), e.deep_view()),
      }
    }
  }

  impl Clone for Prop {
    #[verifier::external_body] fn clone(&self) -> (res: Self) 
    ensures self == res 
    { 
      match self {
        Prop::App(s, v) => Prop::App(s.clone(), v.clone()),
        Prop::Eq(t, e) =>  Prop::Eq(t.clone(), e.clone()),
      }
    }
  }

  impl PartialEq for Prop {
    fn eq(&self, other : &Self) -> bool
    {
      match (self, other) {
        (Prop::App(s, v), Prop::App(t, w)) => s == t && v == w,
        (Prop::Eq(a, b), Prop::Eq(c, d)) => a == c && b == d,

        (Prop::App(_, _), Prop::Eq(_, _)) | (Prop::Eq(_, _), Prop::App(_, _)) => false,
      }
    }
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
      match self {
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

    /* pub open fn SpecSubst(&self, s: &Subst) -> (res: Prop)
    requires self.complete_subst(s)
    ensures res.concrete(),
    {
    match self {
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
  } */

    pub open spec fn symbolic(self) -> bool
    {
      self is App
    }

    pub open spec fn valid(self) -> bool 
    {
      if self.symbolic() == true || self.concrete() == false
      {
        false
      }
      else 
      {
        match self {
          Prop::Eq(x, y) => match (x,y) {
            (Term::Const(x), Term::Const(y)) =>  x == y,
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

  pub struct SpecRule {
    pub head : SpecProp,
    pub body : Seq<SpecProp>,
    pub id : u64,
  }

  impl DeepView for Rule {
    type V = SpecRule;

    open spec fn deep_view(&self) -> Self::V {
      SpecRule {
        head : self.head.deep_view(),
        body : self.body.deep_view(),
        id : self.id,
      }
    }
  }

  impl PartialEq for Rule {
    fn eq(&self, other : &Self) -> bool
    {
      self.head == other.head && self.body == other.body && self.id == other.id
    }
  }

  impl Rule {
    pub open spec fn complete_subst(self, s: &Subst) -> bool {
      self.head.complete_subst(s) && forall| i : int| #![auto] 0 <= i < self.body.len() ==> self.body[i].complete_subst(s)
    }

    pub open spec fn concrete(self) -> bool {
      self.head.concrete() && forall| i : int| #![auto] 0 <= i < self.body.len() ==> self.body[i].concrete()
    }

    pub fn subst(&self, s : &Subst) -> (res : Rule) 
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

  /* pub open spec fn SpecSubst(&self, s : &Subst) -> (res : Rule) 
  recommends self.complete_subst(s)
  
  {
    let mut v = Vec::<Prop>::new();
    for i in 0..self.body.len()
    /invariant 0 <= i <= self.body.len(),
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
  } */

    pub open spec fn wf(self) -> bool {
    self.head.symbolic()
  }
  }

  pub struct RuleSet {
    pub rs : Vec<Rule>
  }

  pub struct SpecRuleSet {
    pub rs : Seq<SpecRule>
  }

  impl DeepView for RuleSet {
    type V = SpecRuleSet;

    open spec fn deep_view(&self) -> Self::V {
      SpecRuleSet {
        rs : self.rs.deep_view(),
      }
    }
  }

  impl RuleSet {
    pub open spec fn wf(self) -> bool {
      forall |i : int| #![auto] 0 <= i < self.rs.len() ==> self.rs[i].wf()
    } 

  /* pub open spec fn contains(self, input : Rule) -> bool 
  {
    self.rs.contains(&input)
  } */

  } 

  pub enum Proof {
    Pstep (Rule, Subst, Vec<Proof>),
    QED (Prop),
  }

  pub enum SpecProof {
    Pstep (SpecRule, SpecSubst, Seq<SpecProof>),
    QED (SpecProp),
  }

  impl DeepView for Proof {
    type V = SpecProof;

    // TODO(pratap): Fix this based on https://github.com/verus-lang/verus/issues/1222
    closed spec fn deep_view(&self) -> Self::V;
  }

  impl PartialEq for Proof {
    fn eq(&self, other : &Self) -> bool
    {
      match (self, other){
        (Proof::Pstep(a, b, c), Proof::Pstep(d, e, f)) => a == d && b == e && c == f,
        (Proof::QED(p), Proof::QED(q)) => p == q ,

        (Proof::Pstep(_, _, _), Proof::QED(_)) | (Proof::QED(_), Proof::Pstep(_, _, _)) => false,
      }
    } 
  }

  impl Proof {
    pub fn head(&self) -> Prop
    requires self matches Proof::Pstep(rule,s,branches) ==> rule.complete_subst(s),
    {
      match self {
        Proof::Pstep(rule, s, branches) => rule.subst(s).head,
        Proof::QED(p) => p.clone(),
      }
    } 

  /* pub open spec fn valid(&self, rule_set: RuleSet) -> bool {
      match self {
        Proof::QED(p) => p.concrete() && !p.symbolic() && p.valid(),
        Proof::Pstep(rule, s, branches) => rule_set.contains(*rule) &&
        rule.complete_subst(s) && rule.body.len() == branches.len() /*  && {
        let rule1 = rule.subst(s); forall |i : int| 0 <= i < rule1.body.len() ==>
        branches[i].valid(rule_set) &&
        rule1.body[i] == branches[i].head()}  */
      }
    } */
 
  } 

  fn main(){
    
  }

}  

    



