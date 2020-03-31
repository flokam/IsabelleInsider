section "Insider Framework"
theory AirInsider
imports MC
begin
datatype action = get | move | eval |put

text \<open>We use an abstract type declaration actor that can later be instantiated by a more 
      concrete type.\<close>
typedecl actor 
consts Actor :: "string \<Rightarrow> actor" 
text \<open>Alternatives to the type declaration do not work.

context
  fixes Abs Rep actor
  assumes td: "type\_definition Abs Rep actor"
begin
definition Actor where "Actor = Abs"
...doesn't work for replacing the actor typedecl because 
in "type\_definition" above the "actor" is a set not a type!
So can't be used for our purposes. 
Trying a locale instead for polymorphic type Actor 
locale ACT =
  fixes Actor :: "string => 'actor"
begin ...
That is a nice idea and works quite far but clashes with the generic
state\_transition later (it's not possible to instantiate within a locale
and outside it we cannot instantiate "'a infrastructure" to state (clearly 
an abstract thing as an instance is strange)\<close>

type_synonym identity = string
type_synonym  policy = "((actor \<Rightarrow> bool) * action set)"

definition ID :: "[actor, string] \<Rightarrow> bool"
where "ID a s \<equiv> (a = Actor s)"

datatype location = Location nat

datatype igraph = Lgraph "(location * location)set" "location \<Rightarrow> identity list"
                         "actor \<Rightarrow> (string list * string list)"  "location \<Rightarrow> string list"
datatype infrastructure = 
         Infrastructure "igraph" 
                        "[igraph, location] \<Rightarrow> policy set" 
                       
primrec loc :: "location \<Rightarrow> nat"
where  "loc(Location n) = n"
primrec gra :: "igraph \<Rightarrow> (location * location)set"
where  "gra(Lgraph g a c l) = g"
primrec agra :: "igraph \<Rightarrow> (location \<Rightarrow> identity list)"
where  "agra(Lgraph g a c l) = a"
primrec cgra :: "igraph \<Rightarrow> (actor \<Rightarrow> string list * string list)"
where  "cgra(Lgraph g a c l) = c"
primrec lgra :: "igraph \<Rightarrow> (location \<Rightarrow> string list)"
where  "lgra(Lgraph g a c l) = l"

definition nodes :: "igraph \<Rightarrow> location set" 
where "nodes g == { x. (? y. ((x,y): gra g) | ((y,x): gra g))}"

definition actors_graph :: "igraph \<Rightarrow> identity set"  
where  "actors_graph g == {x. ? y. y : nodes g \<and> x \<in> set(agra g y)}"

primrec graphI :: "infrastructure \<Rightarrow> igraph"
where "graphI (Infrastructure g d) = g"
primrec delta :: "[infrastructure, igraph, location] \<Rightarrow> policy set"
where "delta (Infrastructure g d) = d"
primrec tspace :: "[infrastructure, actor ] \<Rightarrow> string list * string list"
  where "tspace (Infrastructure g d) = cgra g"
primrec lspace :: "[infrastructure, location ] \<Rightarrow> string list"
where "lspace (Infrastructure g d) = lgra g"

definition credentials :: "string list * string list \<Rightarrow> string set"
  where  "credentials lxl \<equiv> set (fst lxl)"
definition has :: "[igraph, actor * string] \<Rightarrow> bool"
  where "has G ac \<equiv> snd ac \<in> credentials(cgra G (fst ac))"
definition roles :: "string list * string list \<Rightarrow> string set"
  where  "roles lxl \<equiv> set (snd lxl)"
definition role :: "[igraph, actor * string] \<Rightarrow> bool"
  where "role G ac \<equiv> snd ac \<in> roles(cgra G (fst ac))"

definition isin :: "[igraph,location, string] \<Rightarrow> bool" 
  where "isin G l s \<equiv> s \<in> set(lgra G l)"
  
datatype psy_states = happy | depressed | disgruntled | angry | stressed
datatype motivations = financial | political | revenge | curious | competitive_advantage | power | peer_recognition

datatype actor_state = Actor_state "psy_states" "motivations set"
primrec motivation :: "actor_state \<Rightarrow> motivations set" 
where "motivation  (Actor_state p m) =  m"
primrec psy_state :: "actor_state \<Rightarrow> psy_states" 
where "psy_state  (Actor_state p m) = p"

definition tipping_point :: "actor_state \<Rightarrow> bool" where
  "tipping_point a \<equiv> ((motivation a \<noteq> {}) \<and> (happy \<noteq> psy_state a))"

text \<open>UasI and UasI' are the central predicates allowing to specify Insiders.
They define which identities can be mapped to the same role by the Actor function.
For all other identities, Actor is defined as injective on those identities.\<close>
definition UasI ::  "[identity, identity] \<Rightarrow> bool " 
where "UasI a b \<equiv> (Actor a = Actor b) \<and> (\<forall> x y. x \<noteq> a \<and> y \<noteq> a \<and> Actor x = Actor y \<longrightarrow> x = y)"

definition UasI' ::  "[actor => bool, identity, identity] \<Rightarrow> bool " 
where "UasI' P a b \<equiv> P (Actor b) \<longrightarrow> P (Actor a)"

text \<open>Two versions of Insider predicate corresponding to UasI and UasI'.
Under the assumption that the tipping point has been reached for a person a
then a can impersonate all b (take all of b's "roles") where
the b's are specified by a given set of identities \<close>
definition Insider :: "[identity, identity set, identity \<Rightarrow> actor_state] \<Rightarrow> bool" 
where "Insider a C as \<equiv> (tipping_point (as a) \<longrightarrow> (\<forall> b\<in>C. UasI a b))"

definition Insider' :: "[actor \<Rightarrow> bool, identity, identity set, identity \<Rightarrow> actor_state] \<Rightarrow> bool" 
where "Insider' P a C as \<equiv> (tipping_point (as a) \<longrightarrow> (\<forall> b\<in>C. UasI' P a b \<and> inj_on Actor C))"

definition atI :: "[identity, igraph, location] \<Rightarrow> bool" ("_ @\<^bsub>(_)\<^esub> _" 50)
where "a @\<^bsub>G\<^esub> l \<equiv> a \<in> set(agra G l)"

text \<open>enables is the central definition of the behaviour as given by a policy
that specifies what actions are allowed in a certain location for what actors \<close>
definition enables :: "[infrastructure, location, actor, action] \<Rightarrow> bool"
where
"enables I l a a' \<equiv>  (\<exists> (p,e) \<in> delta I (graphI I) l. a' \<in> e \<and> p a)"

text \<open>behaviour is the good behaviour, i.e. everything allowed by policy \<close>
definition behaviour :: "infrastructure \<Rightarrow> (location * actor * action)set"
where "behaviour I \<equiv> {(t,a,a'). enables I t a a'}"

text \<open>misbehaviour is the complement of behaviour \<close>
definition misbehaviour :: "infrastructure \<Rightarrow> (location * actor * action)set"
  where "misbehaviour I \<equiv> -(behaviour I)"

text \<open>basic lemmas for enable\<close>
lemma not_enableI: "(\<forall> (p,e) \<in> delta I (graphI I) l. (~(h : e) | (~(p(a))))) 
                     \<Longrightarrow> ~(enables I l a h)"
  by (simp add: enables_def, blast)

lemma not_enableI2: "\<lbrakk>\<And> p e. (p,e) \<in> delta I (graphI I) l \<Longrightarrow>
                 (~(t : e) |  (~(p(a)))) \<rbrakk> \<Longrightarrow> ~(enables I l a t)"
 by (rule not_enableI, rule ballI, auto)

lemma not_enableE: "\<lbrakk> ~(enables I l a t); (p,e) \<in> delta I (graphI I) l \<rbrakk>
                 \<Longrightarrow> (~(t : e) |  (~(p(a))))"
  by (simp add: enables_def, rule impI, force)

lemma not_enableE2: "\<lbrakk> ~(enables I l a t); (p,e) \<in> delta I (graphI I) l;
                     t : e \<rbrakk> \<Longrightarrow> (~(p(a)))"
  by (simp add: enables_def, force)

text \<open>some constructions to deal with lists of actors in locations for 
the semantics of action move\<close>
primrec del :: "['a, 'a list] \<Rightarrow> 'a list"
where 
del_nil: "del a [] = []" |
del_cons: "del a (x#ls) = (if x = a then ls else x # (del a ls))"

primrec jonce :: "['a, 'a list] \<Rightarrow> bool"
where
jonce_nil: "jonce a [] = False" |
jonce_cons: "jonce a (x#ls) = (if x = a then (a \<notin> (set ls)) else jonce a ls)"

primrec nodup :: "['a, 'a list] \<Rightarrow> bool"
  where 
    nodup_nil: "nodup a [] = True" |
    nodup_step: "nodup a (x # ls) = (if x = a then (a \<notin> (set ls)) else nodup a ls)"

definition move_graph_a :: "[identity, location, location, igraph] \<Rightarrow> igraph"
where "move_graph_a n l l' g \<equiv> Lgraph (gra g) 
                    (if n \<in> set ((agra g) l) &  n \<notin> set ((agra g) l') then 
                     ((agra g)(l := del n (agra g l)))(l' := (n # (agra g l')))
                     else (agra g))(cgra g)(lgra g)"

text \<open>State transition relation over infrastructures (the states) defining the 
   semantics of actions in systems with humans and potentially insiders *)\<close>
inductive state_transition_in :: "[infrastructure, infrastructure] \<Rightarrow> bool" ("(_ \<rightarrow>\<^sub>n _)" 50)
where
  move: "\<lbrakk> G = graphI I; a @\<^bsub>G\<^esub> l; l \<in> nodes G; l' \<in> nodes G;
          (a) \<in> actors_graph(graphI I); enables I l' (Actor a) move;
         I' = Infrastructure (move_graph_a a l l' (graphI I))(delta I) \<rbrakk> \<Longrightarrow> I \<rightarrow>\<^sub>n I'" 
| get : "\<lbrakk> G = graphI I; a @\<^bsub>G\<^esub> l; a' @\<^bsub>G\<^esub> l; has G (Actor a, z);
        enables I l (Actor a) get;
        I' = Infrastructure 
                   (Lgraph (gra G)(agra G)
                           ((cgra G)(Actor a' := 
                                (z # (fst(cgra G (Actor a'))), snd(cgra G (Actor a')))))
                           (lgra G))
                   (delta I)
         \<rbrakk> \<Longrightarrow> I \<rightarrow>\<^sub>n I'"
| put : "\<lbrakk> G = graphI I; a @\<^bsub>G\<^esub> l; enables I l (Actor a) put;
        I' = Infrastructure 
                  (Lgraph (gra G)(agra G)(cgra G)
                          ((lgra G)(l := [z])))
                   (delta I) \<rbrakk>
         \<Longrightarrow> I \<rightarrow>\<^sub>n I'"  
| put_remote : "\<lbrakk> G = graphI I; enables I l (Actor a) put;
        I' = Infrastructure 
                  (Lgraph (gra G)(agra G)(cgra G)
                            ((lgra G)(l := [z])))
                    (delta I) \<rbrakk>
         \<Longrightarrow> I \<rightarrow>\<^sub>n I'"
  
text \<open>show that this infrastructure is a state as given in MC.thy\<close>
instantiation "infrastructure" :: state
begin

definition 
   state_transition_infra_def: "(i \<rightarrow>\<^sub>i i') =  (i \<rightarrow>\<^sub>n (i' :: infrastructure))"

instance
  by (rule MC.class.MC.state.of_class.intro)

definition state_transition_in_refl ("(_ \<rightarrow>\<^sub>n* _)" 50)
where "s \<rightarrow>\<^sub>n* s' \<equiv> ((s,s') \<in> {(x,y). state_transition_in x y}\<^sup>*)"

lemma del_del[rule_format]: "n \<in> set (del a S) \<longrightarrow> n \<in> set S"
  by (induct_tac S, auto)
    
lemma del_dec[rule_format]: "a \<in> set S \<longrightarrow> length (del a S) < length S"  
  by (induct_tac S, auto)

lemma del_sort[rule_format]: "\<forall> n. (Suc n ::nat) \<le> length (l) \<longrightarrow> n \<le> length (del a (l))"   
  by (induct_tac l, simp, clarify, case_tac n, simp, simp)
    
lemma del_jonce: "jonce a l \<longrightarrow> a \<notin> set (del a l)"
  by (induct_tac l, auto)
    
lemma del_nodup[rule_format]: "nodup a l \<longrightarrow> a \<notin> set(del a l)"
  by (induct_tac l, auto)
    
lemma nodup_up[rule_format]: "a \<in> set (del a l) \<longrightarrow> a \<in> set l"
  by (induct_tac l, auto)
    
lemma del_up [rule_format]: "a \<in> set (del aa l) \<longrightarrow> a \<in> set l"
  by (induct_tac l, auto)

lemma nodup_notin[rule_format]:   "a \<notin> set list \<longrightarrow> nodup a list"
  by (induct_tac list, auto)
    
lemma nodup_down[rule_format]: "nodup a l \<longrightarrow> nodup a (del a l)"
  by (induct_tac l, simp+, clarify, erule nodup_notin)

lemma del_notin_down[rule_format]: "a \<notin> set list \<longrightarrow> a \<notin> set (del aa list) "
  by (induct_tac list, auto)

lemma del_not_a[rule_format]: " x \<noteq> a \<longrightarrow> x \<in> set l \<longrightarrow> x \<in> set (del a l)"
  by (induct_tac l, auto)
      
lemma nodup_down_notin[rule_format]: "nodup a l \<longrightarrow> nodup a (del aa l)"
  by (induct_tac l, simp+, rule conjI, clarify, erule nodup_notin, (rule impI)+,
      erule del_notin_down)
    
lemma move_graph_eq: "move_graph_a a l l g = g"  
  by (simp add: move_graph_a_def, case_tac g, force)

text \<open>Some useful properties about the invariance of the nodes, the actors, and the policy 
   with respect to the  state transition\<close> 
lemma delta_invariant: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow>  delta(z) = delta(z')"    
  by (clarify, erule state_transition_in.cases, simp+)

lemma init_state_policy0: 
  assumes "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow>  delta(z) = delta(z')"
      and "(x,y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
    shows "delta(x) = delta(y)"
proof -
  have ind: "(x,y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*
             \<longrightarrow> delta(x) = delta(y)"
  proof (insert assms, erule rtrancl.induct)
    show "(\<And> a::infrastructure.
       (\<forall>(z::infrastructure)(z'::infrastructure). (z \<rightarrow>\<^sub>n z') \<longrightarrow> (delta z = delta z')) \<Longrightarrow>
       (((a, a) \<in> {(x ::infrastructure, y :: infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*) \<longrightarrow>
       (delta a = delta a)))"
    by (rule impI, rule refl)
next fix a b c
  assume a0: "\<forall>(z::infrastructure) z'::infrastructure. z \<rightarrow>\<^sub>n z' \<longrightarrow> delta z = delta z'"
     and a1: "(a, b) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
     and a2: "(a, b) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<longrightarrow>
         delta a = delta b"
     and a3: "(b, c) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}"
     show "(a, c) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<longrightarrow>
       delta a = delta c"
  proof -
    have a4: "delta b = delta c" using a0 a1 a2 a3 by simp
    show ?thesis using a0 a1 a2 a3 by simp
  qed
qed
show ?thesis 
  by (insert ind, insert assms(2), simp)
qed

lemma init_state_policy: "\<lbrakk> (x,y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<rbrakk> \<Longrightarrow> 
                          delta(x) = delta(y)"  
  by (rule init_state_policy0, rule delta_invariant)

lemma same_nodes0[rule_format]: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow> nodes(graphI z) = nodes(graphI z')"   
  by (clarify, erule state_transition_in.cases, 
       (simp add: move_graph_a_def atI_def actors_graph_def nodes_def)+)

lemma same_nodes: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
                   \<Longrightarrow> nodes(graphI y) = nodes(graphI I)"  
  by (erule rtrancl_induct, rule refl, drule CollectD, simp, drule same_nodes0, simp)  

lemma same_actors0[rule_format]: "\<forall> z z'. z \<rightarrow>\<^sub>n z' \<longrightarrow> actors_graph(graphI z) = actors_graph(graphI z')"   
proof (clarify, erule state_transition_in.cases)
  show "\<And>(z::infrastructure) (z'::infrastructure) (G::igraph) (I::infrastructure) (a::char list)
       (l::location) (a'::char list) (za::char list) I'::infrastructure.
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       a' @\<^bsub>G\<^esub> l \<Longrightarrow>
       has G (Actor a, za) \<Longrightarrow>
       enables I l (Actor a) get \<Longrightarrow>
       I' =
       Infrastructure
        (Lgraph (gra G) (agra G)
          ((cgra G)(Actor a' := (za # fst (cgra G (Actor a')), snd (cgra G (Actor a'))))) (lgra G))
        (delta I) \<Longrightarrow>
       actors_graph (graphI z) = actors_graph (graphI z')"
     by (simp add: actors_graph_def nodes_def)
 next show "\<And>(z::infrastructure) (z'::infrastructure) (G::igraph) (I::infrastructure) (a::char list)
       (l::location) (I'::infrastructure) za::char list.
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       enables I l (Actor a) put \<Longrightarrow>
       I' = Infrastructure (Lgraph (gra G) (agra G) (cgra G) ((lgra G)(l := [za]))) (delta I) \<Longrightarrow>
       actors_graph (graphI z) = actors_graph (graphI z')"
   by (simp add: actors_graph_def nodes_def)
next show "\<And>(z::infrastructure) (z'::infrastructure) (G::igraph) (I::infrastructure) (l::location)
       (a::char list) (I'::infrastructure) za::char list.
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       enables I l (Actor a) put \<Longrightarrow>
       I' = Infrastructure (Lgraph (gra G) (agra G) (cgra G) ((lgra G)(l := [za]))) (delta I) \<Longrightarrow>
       actors_graph (graphI z) = actors_graph (graphI z')"
    by (simp add: actors_graph_def nodes_def)
next fix z z' G I a l l' I'
  show "z = I \<Longrightarrow> z' = I' \<Longrightarrow> G = graphI I \<Longrightarrow> a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> nodes G \<Longrightarrow> l' \<in> nodes G \<Longrightarrow> a \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I l' (Actor a) move \<Longrightarrow>
       I' = Infrastructure (move_graph_a a l l' (graphI I)) (delta I) \<Longrightarrow>
       actors_graph (graphI z) = actors_graph (graphI z')"
  proof (rule equalityI)
    show "z = I \<Longrightarrow> z' = I' \<Longrightarrow> G = graphI I \<Longrightarrow> a @\<^bsub>G\<^esub> l \<Longrightarrow>
    l \<in> nodes G \<Longrightarrow> l' \<in> nodes G \<Longrightarrow> a \<in> actors_graph (graphI I) \<Longrightarrow>
    enables I l' (Actor a) move \<Longrightarrow>
    I' = Infrastructure (move_graph_a a l l' (graphI I)) (delta I) \<Longrightarrow>
    actors_graph (graphI z) \<subseteq> actors_graph (graphI z')"
  by (rule subsetI, simp add: actors_graph_def ,(erule exE)+, case_tac "x = a",
      rule_tac x = "l'" in exI, simp add: move_graph_a_def nodes_def atI_def,
      rule_tac x = ya in exI, rule conjI, simp add: move_graph_a_def nodes_def atI_def,
      (erule conjE)+, simp add: move_graph_a_def, rule conjI, clarify,
      simp add: move_graph_a_def nodes_def atI_def, rule del_not_a, assumption+, clarify)
next show "z = I \<Longrightarrow> z' = I' \<Longrightarrow> G = graphI I \<Longrightarrow> a @\<^bsub>G\<^esub> l \<Longrightarrow>
    l \<in> nodes G \<Longrightarrow> l' \<in> nodes G \<Longrightarrow> a \<in> actors_graph (graphI I) \<Longrightarrow>
    enables I l' (Actor a) move \<Longrightarrow>
    I' = Infrastructure (move_graph_a a l l' (graphI I)) (delta I) \<Longrightarrow>
    actors_graph (graphI z') \<subseteq> actors_graph (graphI z)"
  by (rule subsetI, simp add: actors_graph_def, (erule exE)+,
      case_tac "x = a", rule_tac x = "l" in exI, simp add: move_graph_a_def nodes_def atI_def,
      rule_tac x = ya in exI, rule conjI, simp add: move_graph_a_def nodes_def atI_def,
      (erule conjE)+, simp add: move_graph_a_def, case_tac "ya = l", simp,
      case_tac "a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')", simp,
      case_tac "l = l'", simp+, erule del_up, simp,
      case_tac "a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')", simp,
      case_tac "ya = l'", simp+)
qed
qed

lemma same_actors: "(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
              \<Longrightarrow> actors_graph(graphI I) = actors_graph(graphI y)"
proof (erule rtrancl_induct)
  show "actors_graph (graphI I) = actors_graph (graphI I)"
    by (rule refl)
next show "\<And>(y::infrastructure) z::infrastructure.
       (I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       (y, z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
       actors_graph (graphI I) = actors_graph (graphI y) \<Longrightarrow>
       actors_graph (graphI I) = actors_graph (graphI z)"
    by (drule CollectD, simp, drule same_actors0, simp)  
qed

end
end