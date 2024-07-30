use crate::string_hash_map::StringHashMap;
use vstd::assert_seqs_equal;
use vstd::prelude::*;
use vstd::seq::Seq;
use vstd::std_specs::result;

verus! {

pub enum Const {
    Atom(String),
    Nat(u64),
    Str(String),  
}

impl PartialEq for Const {
  // Function alows for Const types to be evaluated for equality and aid Verus verifier; not fully sufficient.
  //Must call const_eq for Atoms and Strs
    fn eq(&self, other: &Self) -> (res: bool)
        ensures
            res <==> self.deep_view() == other.deep_view(),
    {
        match (self, other) {
            (Const::Atom(s), Const::Atom(t)) => s == t,
            (Const::Nat(u), Const::Nat(v)) => u == v,
            (Const::Str(s), Const::Str(t)) => s == t,
            (Const::Atom(_), Const::Nat(_)) | (Const::Nat(_), Const::Atom(_)) => false,
            (Const::Atom(_), Const::Str(_)) | (Const::Str(_), Const::Atom(_)) => false,
            (Const::Str(_), Const::Nat(_)) | (Const::Nat(_), Const::Str(_)) => false,
        }
    }
}

impl Const {
    // uses eq from impl Partial Eq to prove equality between items
    pub fn const_eq(&self, other: &Self) -> (res: bool)
        ensures
            res <==> self.deep_view() == other.deep_view(),
    {
        match (self, other) {
            (Const::Atom(s), Const::Atom(t)) => s.eq(t),
            (Const::Nat(u), Const::Nat(v)) => u == v,
            (Const::Str(s), Const::Str(t)) => s.eq(t),
            _ => false,
        }
    }
}

impl Clone for Const {
    fn clone(&self) -> (res: Self)
        ensures
            self.deep_view() == res.deep_view(),
    {
        match self {
            Const::Atom(s) => Const::Atom(s.clone()),
            Const::Nat(n) => Const::Nat(*n),
            Const::Str(s) => Const::Str(s.clone()),
        }
    }
}

pub enum SpecConst {
    Atom(Seq<char>),
    Nat(u64),  
    Str(Seq<char>),
    
}

impl DeepView for Const {  
    type V = SpecConst;
    // deep_view allows for reasoning about spec-level data structures and types while in exec mode
    open spec fn deep_view(&self) -> Self::V {
        match self {
            Const::Atom(s) => SpecConst::Atom(s.view()),
            Const::Nat(n) => SpecConst::Nat(*n),
            Const::Str(s) => SpecConst::Str(s.view()),
        }
    }
}
// Utilizing StringHashMap from string_hash_map.rs; see relevant functions if needed - not yet in vstd
type Subst = StringHashMap<Const>;
// Using a map with spec-level types to reason about Subst
type SpecSubst = Map<Seq<char>, SpecConst>;

spec fn compatible_subst(s: SpecSubst, t: SpecSubst) -> bool {
    forall|v: String| (#[trigger] s[v@]) == (#[trigger] t[v@])
}

pub enum Term {
    Const(Const),
    Var(String),
}

pub enum SpecTerm {
    Const(SpecConst),
    Var(Seq<char>),
}

impl DeepView for Term {
    type V = SpecTerm;
    // deep_view allows for reasoning about spec-level data structures and types while in exec mode
    open spec fn deep_view(&self) -> Self::V {
        match self {
            Term::Const(c) => SpecTerm::Const(c.deep_view()),
            Term::Var(s) => SpecTerm::Var(s.view()),
        }
    }
}

impl Clone for Term {
    fn clone(&self) -> (res: Self)
        ensures
            self.deep_view() == res.deep_view(),
    {
        match self {
            Term::Var(s) => Term::Var(s.clone()),
            Term::Const(c) => Term::Const(c.clone()),
        }
    }
}

impl PartialEq for Term {
  // Function alows for Term types to be evaluated for equality and aid Verus verifier; not fully sufficient.
    fn eq(&self, other: &Self) -> (res: bool)
        ensures
            res <==> self.deep_view() == other.deep_view(),
    {
        match (self, other) {
            (Term::Const(c), Term::Const(d)) => c == d,
            (Term::Var(s), Term::Var(t)) => s == t,
            (Term::Const(_), Term::Var(_)) | (Term::Var(_), Term::Const(_)) => false,
        }
    }
}

impl SpecTerm {
    pub open spec fn spec_complete_subst(self, s: SpecSubst) -> bool {
        match self {
            SpecTerm::Var(v) => s.contains_key(v),
            SpecTerm::Const(_) => true,
        }
    }

    pub open spec fn spec_concrete(self) -> bool {
        self is Const
    }

    pub open spec fn spec_subst(self, s: SpecSubst) -> (res: SpecTerm)
        recommends
            self.spec_complete_subst(s),
    {
        match self {
            SpecTerm::Var(v) => {
                let u_option = s.index(v);
                SpecTerm::Const(u_option)
            },
            SpecTerm::Const(_) => self,
        }
    }
}

impl Term {
  // function proves equality for Term types
    pub fn term_eq(&self, other: &Self) -> (res: bool)
        ensures
            res <==> self.deep_view() == other.deep_view(),
    {
        match (self, other) {
            (Term::Const(s), Term::Const(t)) => Const::const_eq(&s, &t),
            (Term::Var(u), Term::Var(v)) => u.eq(v),
            _ => false,
        }
    }

    pub fn complete_subst(self, s: &Subst) -> (res: bool)
    // function checks whether Term items are either Const or are Vars with a key in the Subst StringHashMap
        ensures
            res <==> self.deep_view().spec_complete_subst(s.deep_view()),
    {
        match self {
            Term::Var(v) => s.contains_key(v.as_str()),
            Term::Const(_) => true,
        }
    }

    // function checks if term variant is a base type
    pub fn concrete(self) -> (res: bool)
        ensures
            res <==> self.deep_view().spec_concrete(),
    {
        match self {
            Term::Const(_) => true,
            Term::Var(_) => false,
        }
    }

    // this functions performs a substitution to achieve a Const variant of Term
    pub fn subst(self, s: &Subst) -> (res: Term)
        requires
            self.deep_view().spec_complete_subst(s.deep_view()),
        ensures
            res.deep_view().spec_concrete(),
            res.deep_view() == self.deep_view().spec_subst(s.deep_view()),
    {
        match self {
            Term::Var(v) => {
                let u_option = s.get(v.as_str());
                Term::Const(u_option.unwrap().clone())
            },
            Term::Const(_) => self,
        }
    }
}

# [verifier::external_body]
pub fn terms_eq(a: &Vec<Term>, b: &Vec<Term>) -> (res: bool)
    ensures
        res <==> a.deep_view() == b.deep_view(),
{
    a == b
}

pub enum Prop {
    App(String, Vec<Term>),
    Eq(Term, Term),
}

pub enum SpecProp {
    App(Seq<char>, Seq<SpecTerm>),
    Eq(SpecTerm, SpecTerm),
}

impl DeepView for Prop {
    type V = SpecProp;
     // deep_view allows for reasoning about spec-level data structures and types while in exec mode
    open spec fn deep_view(&self) -> Self::V {
        match self {
            Prop::App(s, v) => SpecProp::App(s.view(), v.deep_view()),
            Prop::Eq(t, e) => SpecProp::Eq(t.deep_view(), e.deep_view()),
        }
    }
}

impl Clone for Prop {
    #[verifier::external_body]
    fn clone(&self) -> (res: Self)
        ensures
            self == res,
    {
        match self {
            Prop::App(s, v) => Prop::App(s.clone(), v.clone()),
            Prop::Eq(t, e) => Prop::Eq(t.clone(), e.clone()),
        }
    }
}

impl PartialEq for Prop {
  // function aids verus verifier in reasoning baout equality; not fully sufficient - must call prop_eq for certain types
    fn eq(&self, other: &Self) -> (res: bool)
        ensures
            res <==> self.deep_view() == other.deep_view(),
    {
        match (self, other) {
            (Prop::App(s, v), Prop::App(t, w)) => s == t && v == w,
            (Prop::Eq(a, b), Prop::Eq(c, d)) => a == c && b == d,
            (Prop::App(_, _), Prop::Eq(_, _)) | (Prop::Eq(_, _), Prop::App(_, _)) => false,
        }
    }
}

impl SpecProp {
  // function checks if Prop variants contain key to map; calls spec_complete_subst from Term
    pub open spec fn spec_complete_subst(self, s: SpecSubst) -> bool {
        match self {
            SpecProp::App(head, args) => forall|i: int|
                #![auto]
                0 <= i < args.len() ==> args[i].spec_complete_subst(s),
            SpecProp::Eq(x, y) => x.spec_complete_subst(s) && y.spec_complete_subst(
                s,
            )
        }
    }

    // checks if Prop variants are of base types
    pub open spec fn spec_concrete(self) -> bool {
        match self {
            SpecProp::App(head, args) => forall|i: int|
                #![auto]
                0 <= i < args.len() ==> args[i].spec_concrete(),
            SpecProp::Eq(x, y) => x.spec_concrete() && y.spec_concrete(),
        }
    }

    pub open spec fn spec_symbolic(self) -> bool {
        self is App
    }

    // function checks whether valid SpecProp types are concrete and are equal
    pub open spec fn spec_valid(self) -> bool {
        if self.spec_symbolic() == true || self.spec_concrete() == false {
            false
        } else {
            match self {
                SpecProp::Eq(x, y) => match (x, y) {
                    (SpecTerm::Const(x), SpecTerm::Const(y)) => x == y,
                    (SpecTerm::Var(x), SpecTerm::Var(y)) => false,
                    (SpecTerm::Const(_), SpecTerm::Var(_))
                    | (SpecTerm::Var(_), SpecTerm::Const(_)) => false,
                },
                SpecProp::App(s, v) => false,
            }
        }
    }
    // reasons about substitution of SpecProp variants
    pub open spec fn spec_subst(self, s: SpecSubst) -> (res: SpecProp)
        recommends
            self.spec_complete_subst(s),
    {
        match self {
            SpecProp::App(h, args) => {
                let new_sequence = args.map_values(|p: SpecTerm| p.spec_subst(s));
                SpecProp::App(h, new_sequence)
            },
            SpecProp::Eq(x, y) => SpecProp::Eq(x.spec_subst(s), y.spec_subst(s)),
        }
    }
}

impl Prop {
  // proves equality for Prop types. uses term_eq and terms_eq
    pub fn prop_eq(&self, other: &Self) -> (res: bool)
        ensures
            res <==> self.deep_view() == other.deep_view(),
    {
        match (self, other) {
            (Prop::App(a, b), Prop::App(c, d)) => a.eq(c) && terms_eq(b, d),
            (Prop::Eq(h, i), Prop::Eq(j, k)) => Term::term_eq(h, j) && Term::term_eq(i, k),
            _ => false,
        }
    }
    // function checks whether Prop variants are concrete and elements are equal to each other
    pub fn valid(self) -> (res: bool)
        requires
            !self.deep_view().spec_symbolic(),
            self.deep_view().spec_concrete(),
        ensures
            res <==> self.deep_view().spec_valid(),
    {
        match self {
            Prop::Eq(x, y) => match (x, y) {
                (Term::Const(x), Term::Const(y)) => Const::const_eq(&x, &y),
                (Term::Var(x), Term::Var(y)) => false,
                (Term::Const(_), Term::Var(_)) | (Term::Var(_), Term::Const(_)) => false,
            },
            Prop::App(s, v) => false,
        }
    }

    pub fn symbolic(self) -> (res: bool)
        ensures
            res <==> self.deep_view().spec_symbolic(),
    {
        match self {
            Prop::App(_, _) => true,
            Prop::Eq(_, _) => false,
        }
    }

    //checks whether Prop variants are base types
    pub fn concrete(self) -> (res: bool)
        ensures
            res <==> self.deep_view().spec_concrete(),
    {
        match self {
            Prop::App(head, args) => {
                assert(match self.deep_view() {
                    SpecProp::App(_, spec_args) => forall|k: int|
                        0 <= k < args.len() ==> (#[trigger] args[k].deep_view()) == spec_args[k],
                    SpecProp::Eq(_, _) => true,
                });
                let mut flag = true;
                for i in 0..args.len()
                    invariant
                        0 <= i <= args.len(),
                        flag <==> forall|j: int|
                            #![auto]
                            0 <= j < i ==> args[j].deep_view().spec_concrete(),
                {
                    flag = args[i].clone().concrete() && flag;
                }
                flag
            },
            Prop::Eq(x, y) => x.concrete() && y.concrete(),
        }
    }

    // checks if Prop variants contain key in Susbt StringHashMap
    pub fn complete_subst(&self, s: &Subst) -> (res: bool)
        ensures
            res <==> self.deep_view().spec_complete_subst(s.deep_view()),
    {
        match self {
            Prop::App(head, args) => {
                assert(match self.deep_view() {
                    SpecProp::App(_, spec_args) => forall|k: int|
                        0 <= k < args.len() ==> (#[trigger] args[k].deep_view()) == spec_args[k],
                    SpecProp::Eq(_, _) => true,
                });
                let mut flag = true;
                for i in 0..args.len()
                    invariant
                        0 <= i <= args.len(),
                        flag <==> forall|j: int|
                            #![auto]
                            0 <= j < i ==> args[j].deep_view().spec_complete_subst(s.deep_view()),
                {
                    flag = args[i].clone().complete_subst(s) && flag;
                }
                flag
            },
            Prop::Eq(x, y) => x.clone().complete_subst(s) && y.clone().complete_subst(
                s,
            )
        }
    }

    //performs substitution on Prop types and converts them to base types
    pub fn subst(&self, s: &Subst) -> (res: Prop)
        requires
            self.deep_view().spec_complete_subst(s.deep_view()),
        ensures
            res.deep_view() == self.deep_view().spec_subst(s.deep_view()),
            res.deep_view().spec_concrete(),
    {
        match self {
            Prop::App(h, args) => {
                assert(match self.deep_view() {
                    SpecProp::App(_, spec_args) => forall|k: int|
                        0 <= k < args.len() ==> (#[trigger] args[k].deep_view()) == spec_args[k],
                    SpecProp::Eq(_, _) => true,
                });
                let mut v = Vec::<Term>::new();
                for i in 0..args.len()
                    invariant
                        0 <= i <= args.len(),
                        v.len() == i,
                        forall|j: int|
                            0 <= j < args.deep_view().len() ==> (
                            #[trigger] args[j as int].deep_view().spec_complete_subst(
                                s.deep_view(),
                            )),
                        forall|j: int|
                            #![auto]
                            0 <= j < i ==> args[j].deep_view().spec_subst(s.deep_view())
                                == v[j].deep_view(),
                        forall|j: int| #![auto] 0 <= j < i ==> v[j].deep_view().spec_concrete(),
                {
                    v.push(args[i].clone().subst(s));
                }
                proof {
                    assert_seqs_equal!(v.deep_view(), args.deep_view().map_values(|p: SpecTerm| p.spec_subst(s.deep_view())));
                }
                ;
                Prop::App(h.clone(), v)
            },
            Prop::Eq(x, y) => Prop::Eq(x.clone().subst(s), y.clone().subst(s)),
        }
    }
}

pub struct Rule {
    pub head: Prop,
    pub body: Vec<Prop>,
    pub id: u64,
}

pub struct SpecRule {
    pub head: SpecProp,
    pub body: Seq<SpecProp>,
    pub id: u64,
}

impl DeepView for Rule {
    type V = SpecRule;

    open spec fn deep_view(&self) -> Self::V {
        SpecRule { head: self.head.deep_view(), body: self.body.deep_view(), id: self.id }
    }
}

impl PartialEq for Rule {
    fn eq(&self, other: &Self) -> (res: bool)
        ensures
            res <==> self.deep_view() == other.deep_view(),
    {
        self.head == other.head && self.body == other.body && self.id == other.id
    }
}

impl Clone for Rule {
    #[verifier::external_body]
    fn clone(&self) -> (res: Self)
        ensures
            self == res,
    {
        Rule { head: self.head.clone(), body: self.body.clone(), id: self.id.clone() }
    }
}

impl SpecRule {
    pub open spec fn spec_complete_subst(self, s: SpecSubst) -> bool {
        &&& self.head.spec_complete_subst(s)
        &&& forall|i: int| #![auto] 0 <= i < self.body.len() ==> self.body[i].spec_complete_subst(s)
    }

    pub open spec fn spec_concrete(self) -> bool {
        self.head.spec_concrete() && forall|i: int|
            #![auto]
            0 <= i < self.body.len() ==> self.body[i].spec_concrete()
    }

    pub open spec fn spec_wf(self) -> bool {
        self.head.spec_symbolic()
    }

    pub open spec fn spec_subst(self, s: SpecSubst) -> (res: SpecRule)
        recommends
            self.spec_complete_subst(s),
    {
        let new_sequence = self.body.map_values(|p: SpecProp| p.spec_subst(s));
        let result = SpecRule { head: self.head.spec_subst(s), body: new_sequence, id: self.id };
        result
    }
}

impl Rule {
    pub fn subst(&self, s: &Subst) -> (res: Rule)
        requires
            self.deep_view().spec_complete_subst(s.deep_view()),
        ensures
            res.deep_view().spec_concrete(),
            res.deep_view() == self.deep_view().spec_subst(s.deep_view()),
            res.body.view().len() == self.body.view().len(),
    {
        let mut v = Vec::<Prop>::new();
        assert(forall|k: int|
            0 <= k < self.body.len() ==> (#[trigger] self.body[k].deep_view())
                == self.deep_view().body[k]);
        for i in 0..self.body.len()
            invariant
                0 <= i <= self.body.len(),
                v.len() == i,
                forall|i: int|
                    #![auto]
                    0 <= i < self.body.deep_view().len()
                        ==> self.body[i].deep_view().spec_complete_subst(s.deep_view()),
                forall|j: int|
                    #![auto]
                    0 <= j < i ==> self.body[j].deep_view().spec_subst(s.deep_view())
                        == v[j].deep_view(),
                forall|j: int| #![auto] 0 <= j < i ==> v[j].deep_view().spec_concrete(),
        {
            v.push(self.body[i].subst(s));
        }
        proof {
            assert_seqs_equal!(v.deep_view(), self.body.deep_view().map_values(|p: SpecProp| p.spec_subst(s.deep_view())));
        }
        ;
        let result = Rule { head: self.head.subst(s), body: v, id: self.id };
        result
    }

    pub fn complete_subst(&self, s: &Subst) -> (res: bool)
        ensures
            res <==> self.deep_view().spec_complete_subst(s.deep_view()),
    {
        self.head.complete_subst(s) && {
            assert(forall|k: int|
                0 <= k < self.body.len() ==> (#[trigger] self.body[k].deep_view())
                    == self.deep_view().body[k]);
            let mut flag = true;
            for i in 0..self.body.len()
                invariant
                    0 <= i <= self.body.len(),
                    flag <==> forall|j: int|
                        #![auto]
                        0 <= j < i ==> self.body[j].deep_view().spec_complete_subst(s.deep_view()),
            {
                flag = self.body[i].clone().complete_subst(s) && flag
            }
            flag
        }
    }

    pub fn concrete(&self) -> (res: bool)
        ensures
            res <==> self.deep_view().spec_concrete(),
    {
        self.head.clone().concrete() && {
            assert(forall|k: int|
                0 <= k < self.body.len() ==> (#[trigger] self.body[k].deep_view())
                    == self.deep_view().body[k]);
            let mut flag = true;
            for i in 0..self.body.len()
                invariant
                    0 <= i <= self.body.len(),
                    flag <==> forall|j: int|
                        #![auto]
                        0 <= j < i ==> self.body[j].deep_view().spec_concrete(),
            {
                flag = self.body[i].clone().concrete() && flag
            }
            flag
        }
    }

    pub fn wf(&self) -> (res: bool)
        ensures
            res <==> self.deep_view().spec_wf(),
    {
        self.head.clone().symbolic()
    }
}

pub struct RuleSet {
    pub rs: Vec<Rule>,
}

pub struct SpecRuleSet {
    pub rs: Seq<SpecRule>,
}

impl DeepView for RuleSet {
    type V = SpecRuleSet;

    open spec fn deep_view(&self) -> Self::V {
        SpecRuleSet { rs: self.rs.deep_view() }
    }
}

impl SpecRuleSet {
    pub open spec fn spec_wf(self) -> bool {
        forall|i: int| #![auto] 0 <= i < self.rs.len() ==> self.rs[i].spec_wf()
    }
}

impl RuleSet {
    pub fn wf(self) -> (res: bool)
        ensures
            res <==> self.deep_view().spec_wf(),
    {
        let mut flag = true;
        assert(forall|k: int|
            0 <= k < self.rs.len() ==> (#[trigger] self.rs[k].deep_view())
                == self.deep_view().rs[k]);
        for i in 0..self.rs.len()
            invariant
                0 <= i <= self.rs.len(),
                flag <==> forall|j: int| #![auto] 0 <= j < i ==> self.rs[j].deep_view().spec_wf(),
        {
            flag = self.rs[i].wf() && flag
        }
        flag
    }
}

pub enum Proof {
    Pstep(Rule, Subst, Vec<Proof>),
    QED(Prop),
}

pub enum SpecProof {
    Pstep(SpecRule, SpecSubst, Seq<SpecProof>),
    QED(SpecProp),
}

impl DeepView for Proof {
    type V = SpecProof;
    closed spec fn deep_view(&self) -> Self::V;
}

#[verifier::external_body]
pub proof fn axiom_proof_deep_view(pf: &Proof)
    ensures 
        pf matches Proof::Pstep(r, s, v) ==> 
          (#[trigger] pf.deep_view()) matches SpecProof::Pstep(spec_r, spec_s, spec_v)
          && r.deep_view() == spec_r && s.deep_view() == spec_s && v.deep_view() == spec_v,
        pf matches Proof::QED(p) ==> 
          pf.deep_view() matches SpecProof::QED(spec_p)
          && p.deep_view() == spec_p,
{}

impl PartialEq for Proof {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Proof::Pstep(a, b, c), Proof::Pstep(d, e, f)) => a == d && b == e && c == f,
            (Proof::QED(p), Proof::QED(q)) => p == q,
            (Proof::Pstep(_, _, _), Proof::QED(_))
            | (Proof::QED(_), Proof::Pstep(_, _, _)) => false,
        }
    }
}

impl Clone for Proof {
    #[verifier::external_body]
    fn clone(&self) -> (res: Self)
        ensures
            self == res,
    {
        match self {
            Proof::Pstep(r, s, v) => Proof::Pstep(r.clone(), s.clone(), v.clone()),
            Proof::QED(p) => Proof::QED(p.clone()),
        }
    }
}

impl SpecProof {
    pub open spec fn spec_valid(self, rule_set: SpecRuleSet) -> bool
        decreases self,
    {
        match self {
            SpecProof::QED(p) => p.spec_concrete() && !p.spec_symbolic() && p.spec_valid(),
            SpecProof::Pstep(rule, s, branches) => rule_set.rs.contains(rule)
                && rule.spec_complete_subst(s) && rule.body.len() == branches.len() && {
                let rule1 = rule.spec_subst(s);
                forall|i: int|
                    #![auto]
                    0 <= i < rule1.body.len() ==> branches[i].spec_valid(rule_set) && rule1.body[i]
                        == branches[i].spec_head()
            },
        }
    }

    pub open spec fn spec_head(self) -> SpecProp
        recommends
            self matches SpecProof::Pstep(rule, s, branches) ==> rule.spec_complete_subst(s),
    {
        match self {
            SpecProof::Pstep(rule, s, branches) => rule.spec_subst(s).head,
            SpecProof::QED(p) => p,
        }
    }
}

impl Proof {
    pub fn head(&self) -> (res: Prop)
        requires
            self matches Proof::Pstep(rule, s, branches) ==> rule.deep_view().spec_complete_subst(
                s.deep_view(),
            ),
        ensures
            res.deep_view() <==> self.deep_view().spec_head(),
    {
        proof { axiom_proof_deep_view(self) };
        match self {
            Proof::Pstep(rule, s, branches) => rule.subst(s).head,
            Proof::QED(p) => p.clone(),
        }
    }
}

pub struct Thm {
    pub val: Prop,
    pub p: Proof,
}

pub struct SpecThm {
    pub val: SpecProp,
    pub p: SpecProof,
}

impl DeepView for Thm {
    type V = SpecThm;

    open spec fn deep_view(&self) -> Self::V {
        SpecThm { val: self.val.deep_view(), p: self.p.deep_view() }
    }
}

impl SpecThm {
    pub open spec fn spec_wf(self, rule_set: SpecRuleSet) -> bool {
        self.p.spec_valid(rule_set) && self.p.spec_head() == self.val
    }
}

pub fn mk_leaf(p: &Prop) -> (res: Result<Thm, ()>)
    ensures
        p.deep_view().spec_concrete() && !p.deep_view().spec_symbolic()
            && p.deep_view().spec_valid() ==> res.is_Ok(),
        res matches Ok(v) ==> v.val == p,
{
    if p.clone().concrete() && !p.clone().symbolic() && p.clone().valid() {
        Ok(Thm { val: p.clone(), p: Proof::QED(p.clone()) })
    } else {
        Err(())
    }
}

#[verifier::loop_isolation(false)]
pub fn mk_thm(rs: &RuleSet, k: usize, s: &Subst, args: &Vec<Thm>) -> (res: Result<Thm, ()>)
    requires
        k < rs.rs.len(),
        forall|j: int| #![auto] 0 <= j < args.len() ==> args[j].deep_view().spec_wf(rs.deep_view()),
    ensures
        ((rs.rs[k as int].deep_view().spec_complete_subst(s.deep_view()) && args.len()
            == rs.rs[k as int].body.len() && (forall|j: int|
            #![auto]
            0 <= j < args.len() ==> args[j].deep_view().val
                == rs.rs[k as int].deep_view().spec_subst(s.deep_view()).body[j])) ==> res.is_Ok()),
        res matches Ok(thm) ==> 
            rs.rs[k as int].deep_view().spec_complete_subst(s.deep_view())
            && thm.deep_view().spec_wf(rs.deep_view()) 
            && thm.deep_view().val == rs.rs[k as int].deep_view().spec_subst(s.deep_view()).head,
{
    let r = rs.rs[k].clone();
    assert(rs.deep_view().rs[k as int] == r.deep_view());
    assert(rs.deep_view().rs.contains(r.deep_view()));
    if args.len() != r.body.len() || !r.complete_subst(&s) {
        return Err(());
    }
    let mut flag = true;
    let r_subst = r.subst(&s);
    assert(r_subst.deep_view() == r.deep_view().spec_subst(s.deep_view()));
    assert(r_subst.body.view().len() == r.body.view().len());
    for i in 0..args.len()
        invariant
            0 <= i <= args.len(),
            r_subst.body.view().len() == r.body.view().len(),
            r_subst.deep_view() == r.deep_view().spec_subst(s.deep_view()),
            flag <==> forall|j: int|
                #![auto]
                0 <= j < i ==> args[j as int].deep_view().val == r_subst.deep_view().body[j as int],
    {
        flag = (Prop::prop_eq(&r_subst.body[i], &args[i].val) && flag);
        assert(flag ==> args[i as int].deep_view().val == r_subst.deep_view().body[i as int]);
    }
    if flag == true {
        let mut pfs: Vec<Proof> = Vec::new();
        for i in 0..args.len()
            invariant
                pfs.len() == i,
                0 <= i <= args.len(),
                forall |j: int| #![auto] 0 <= j < i ==> pfs[j].deep_view().spec_valid(rs.deep_view()), 
                forall |j: int| #![auto] 0 <= j < i ==> r_subst.deep_view().body[j] == pfs[j].deep_view().spec_head()
        {
            pfs.push(args[i].p.clone());
            proof { axiom_proof_deep_view(&args[i as int].p) };
        }
        let p = Proof::Pstep(r.clone(), s.clone(), pfs);
        let thm = Thm { val: r_subst.head, p: p };
        proof { axiom_proof_deep_view(&p) };
        Ok(thm)
    } else {
        Err(())
    }
}

fn main() {
}

} // verus!
