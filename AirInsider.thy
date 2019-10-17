theory AirInsider
imports Main
begin
datatype action = get | move | eval |put
typedecl actor 
type_synonym identity = string
consts Actor :: "string => actor"
type_synonym policy = "((actor => bool) * action set)"

definition ID :: "[actor, string] \<Rightarrow> bool"
where "ID a s \<equiv> (a = Actor s)"

datatype location = Location nat
(* So, we need to fill tspace and lspace with a semantics based on the state i.e.
   the graph/infrastructure. An idea would be to have tables for 
   role(Actor x, r) and has(Actor y, c) as well as for locations
   for isin l s .  The tables would then be the basis for proper semantic definitions
   of the operators tspace and lspace. For example tspace (Actor a) a would not return
   just bool but all roles and credentials that the actor has. A policy would still
   state has (x,''PIN'') for example but the ex_creds map would assign a pair of lists
   instead of bool. 
   Semantics of has could be achieved by extending the type with infrastructure
   has :: [infrastructure, (actor *string)] \<Rightarrow> bool but with semantics
   "has I (a, c) == (a,c) \in credentials(tspace I a)
   where credential is an acronym for lambda lxl. set(first lxl)
   similar for role with projection roles lxl = set(snd lxl) 
   [infrastructure, (actor *string)] \<Rightarrow> bool where
   role I (a, r) == (a, r) \in roles(tspace I a)
   For lspace we need to define isin
   isin :: [infrastructure, location, string] \<Rightarrow> bool where
   isin I l s == (l,s) \in set(lspace I l) 
   we don't need projections here since lspace is just one table
   (i.e. list of pairs (location * string)).
*)  
datatype igraph = Lgraph "(location * location)set" "location \<Rightarrow> identity list"
                         "actor \<Rightarrow> (string list * string list)"  "location \<Rightarrow> string list"
datatype infrastructure = 
         Infrastructure "igraph" 
                        "[igraph ,location] \<Rightarrow> policy set" 
                       
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

(* idea:: predicate to flag that an actor is isolated *)
consts Isolation :: "[actor_state, (identity * identity) set ] \<Rightarrow> bool"


(* use above to redefine infrastructure -- adapt policies in nodes
   so that layed off workers cannot access any more *)
definition lay_off :: "[infrastructure,actor set] \<Rightarrow> infrastructure"
where "lay_off G A \<equiv> G"

(* idea: social graph is derived from activities in infrastructure.
   Since actors are nodes in the infrastructure graph, we need to 
   have a second graph only on actors reflecting their interaction. *)
consts social_graph :: "(identity * identity) set"
(* This social graph is a parameter to the theory. It depends on
   actual measured activities. We will use it to derive meta-theorems. *)

definition UasI ::  "[identity, identity] \<Rightarrow> bool " 
where "UasI a b \<equiv> (Actor a = Actor b) \<and> (\<forall> x y. x \<noteq> a \<and> y \<noteq> a \<and> Actor x = Actor y \<longrightarrow> x = y)"

definition UasI' ::  "[actor => bool, identity, identity] \<Rightarrow> bool " 
where "UasI' P a b \<equiv> P (Actor b) \<longrightarrow> P (Actor a)"

(* derive theorems about UasI being a equivalence relation *)

consts astate :: "identity \<Rightarrow> actor_state"

definition Insider :: "[identity, identity set] \<Rightarrow> bool" 
where "Insider a C \<equiv> (tipping_point (astate a) \<longrightarrow> (\<forall> b\<in>C. UasI a b))"


definition Insider' :: "[actor \<Rightarrow> bool, identity, identity set] \<Rightarrow> bool" 
where "Insider' P a C \<equiv> (tipping_point (astate a) \<longrightarrow> (\<forall> b\<in>C. UasI' P a b \<and> inj_on Actor C))"

(* restriction in new version for WRIT 16 *)
definition atI :: "[identity, igraph, location] \<Rightarrow> bool" ("_ @\<^bsub>(_)\<^esub> _" 50)
where "a @\<^bsub>G\<^esub> l \<equiv> a \<in> set(agra G l)"

(* enables needs  (\<exists> n. ID a n \<and> (n @\<^bsub>graphI I\<^esub> l)\<or> connected I n l) *) 
definition enables :: "[infrastructure, location, actor, action] \<Rightarrow> bool"
where
"enables I l a a' \<equiv>  (\<exists> (p,e) \<in> delta I (graphI I) l. a' \<in> e \<and> p a)"


(* behaviour is the good behaviour, i.e. everything allowed by policy *)
definition behaviour :: "infrastructure \<Rightarrow> (location * actor * action)set"
where "behaviour I \<equiv> {(t,a,a'). enables I t a a'}"

(* somewhat to special I find now:
definition misbehaviour :: "infrastructure \<Rightarrow> (location * identity * action)set"
where "misbehaviour I \<equiv> {(t,a,a'). \<exists> b. UasI a b \<and> enables I t (Actor b) a'}"
*)
(* Most general: misbehaviour is the complement of behaviour *)
definition misbehaviour :: "infrastructure \<Rightarrow> (location * actor * action)set"
where "misbehaviour I \<equiv> -(behaviour I)"

end
