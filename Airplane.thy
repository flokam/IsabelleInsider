section \<open>Airplane case study\<close>
text \<open>In this section we first provide the necessary infrastructure, then
specify global and local policies, and finally formalize insider
attacks and safety and security.\<close>
theory Airplane
imports AirInsider
begin
(*
text \<open>Locations  of the infrastructure graph have specific states.
For example, the door can be in state @{text \<open>locked\<close>}.\<close>
datatype doorstate = locked | norm | unlocked
datatype position = air | airport | ground
*)
subsection \<open>Formalization of Airplane Infrastructure and Properties\<close>
text \<open>We restrict the Airplane scenario to four identities: Bob, Charly, Alice, and Eve.
Bob acts as the pilot, Charly as the copilot, and Alice as the flight attendant. 
Eve is an identity representing the malicious agent that can act as the copilot
although not officially acting as an airplane actor. The identities that act
legally inside the airplane infrastructure are listed in the set
of airplane actors.

To represent the layout of the airplane, a simple architecture is best suited
for the purpose of security policy verification. The locations we consider for
the graph are @{text \<open>cockpit\<close>}, @{text \<open>door\<close>}, and @{text \<open>cabin\<close>}. They are
defined as locale definitions and assembled in a set @{text \<open>airplane_locations\<close>}.

The actual layout and the initial distribution of the actors in the 
airplane infrastructure is defined by the graph @{text \<open>ex_graph\<close>} in which 
the actors Bob and Charly are in the cockpit and Alice is in the 
cabin.

The two additional inputs @{text \<open>ex_creds\<close>} and @{text \<open>ex_locs\<close>} 
for the constructor @{text \<open>Lgraph\<close>} are the credential and role assignment 
to actors and the state function for locations introduced in Section 
\ref{sec:infra}, respectively. For the airplane scenario, we use 
the function @{text \<open>ex_creds\<close>} to assign the roles and credentials 
to actors. For example, for @{text \<open>Actor ''Bob''\<close>} this 
function returns the pair of lists @{text \<open>([''PIN''], [''pilot''])\<close>}
assigning the credential @{text \<open>PIN\<close>} to this actor and 
designating the role @{text \<open>pilot\<close>} to him.
Similar to the previous function @{text \<open>ex_creds\<close>}, 
the function @{text \<open>ex_locs\<close>} assigns values to the locations
of the infrastructure graph. These values are simply of type string allowing to 
store arbitrary state information about the locations, for example, the door is
"locked" or the airplane is on the "ground".

In the Isabelle Insider framework, we define a global policy reflecting
the global safety and security goal and then break that down into local 
policies on the infrastructure. The verification will then analyze whether
the infrastructure's local policies yield the global policy.

subsection \<open>Initial Global and Local Policies\<close>
Globally, we want to exclude attackers to ground the plane. In the 
formal model, landing the airplane results from an actor performing a
@{text \<open>put\<close>} action in the cockpit and 
thereby changing the state from @{text \<open>air\<close>} to @{text \<open>ground\<close>}.

Therefore, we specify the global policy as ``no one except
airplane actors can perform @{text \<open>put\<close>} actions at location cockpit''
by the following predicate over infrastructures @{text \<open>I\<close>} and
actor identities @{text \<open>a\<close>}.

We next attempt to define the @{text \<open>local_policies\<close>} for each location as a function
mapping locations to sets of pairs: the first element of each pair for a location 
@{text \<open>l\<close>} is a predicate over actors specifying the conditions necessary for an actor
to be able to perform the actions specified in the set of actions which is the
second element of that pair.
Local policy functions are additionally parameterized over an infrastructure
graph @{text \<open>G\<close>} since this may dynamically change through the state transition. 
The policy @{text \<open>local_policies\<close>} expresses that any actor can move to door and cabin but
places the following restrictions on cockpit.
\begin{description}
\item[@{text \<open>put\<close>}:] to perform a @{text \<open>put\<close>} action, that is, put the plane into a new position 
            or put the lock, an actor must be at position cockpit, i.e., in the cockpit;
\item[@{text \<open>move\<close>}:] to perform a move action at location cockpit, that is, move into it,
             an actor must be at the position cabin, must be in possession of 
             PIN, and door must be in state norm.
\end{description}
Although this policy abstracts from the buzzer, the 30 sec delay, and a few
other technical details, it captures the essential features of the cockpit door.

The graph, credentials, and features are plugged together with the policy 
into the infrastructure @{text \<open>Airplane_scenario\<close>}.\<close>

locale airplane =

fixes airplane_actors :: "identity set"
defines airplane_actors_def: "airplane_actors \<equiv> {''Bob'', ''Charly'', ''Alice''}"

fixes airplane_locations :: "location set"
defines airplane_locations_def: 
"airplane_locations \<equiv> {Location 0, Location 1, Location 2}"
(* 0 cabin, 1 door, 2 cockpit *)
fixes cockpit :: "location"
defines cockpit_def: "cockpit \<equiv> Location 2" 
fixes door :: "location"
defines door_def: "door \<equiv> Location 1" 
fixes cabin :: "location"
defines cabin_def: "cabin \<equiv> Location 0" 

fixes global_policy :: "[infrastructure, identity] \<Rightarrow> bool"
defines global_policy_def: "global_policy I a \<equiv> a \<notin> airplane_actors 
                 \<longrightarrow> \<not>(enables I cockpit (Actor a) put)"

fixes ex_creds :: "actor  \<Rightarrow> (string list * string list)"
defines ex_creds_def: "ex_creds \<equiv> 
        (\<lambda> x.(if x = Actor ''Bob'' 
              then ([''PIN''], [''pilot''])        
              else (if x = Actor ''Charly'' 
                    then ([''PIN''],[''copilot''])
                    else (if x = Actor ''Alice''  
                          then ([''PIN''],[''flightattendant''])
                                else ([],[])))))"

fixes ex_locs :: "location \<Rightarrow> string list"
defines ex_locs_def: "ex_locs \<equiv>  (\<lambda> x. if x = door then [''norm''] else 
                                       (if x = cockpit then [''air''] else []))"
  
fixes ex_locs' :: "location \<Rightarrow> string list"
defines ex_locs'_def: "ex_locs' \<equiv>  (\<lambda> x. if x = door then [''locked''] else
                                         (if x = cockpit then [''air''] else []))"
fixes ex_graph :: "igraph"
defines ex_graph_def: "ex_graph \<equiv> Lgraph
      {(cockpit, door),(door,cabin)}
      (\<lambda> x. if x = cockpit then [''Bob'', ''Charly''] 
            else (if x = door then [] 
                  else (if x = cabin then [''Alice''] else [])))
      ex_creds ex_locs"

fixes aid_graph :: "igraph"
defines aid_graph_def: "aid_graph \<equiv>  Lgraph
      {(cockpit, door),(door,cabin)}
      (\<lambda> x. if x = cockpit then [''Charly''] 
            else (if x = door then [] 
                  else (if x = cabin then [''Bob'', ''Alice''] else [])))
      ex_creds ex_locs'"
  
fixes aid_graph0 :: "igraph"
defines aid_graph0_def: "aid_graph0 \<equiv>  Lgraph
      {(cockpit, door),(door,cabin)}
      (\<lambda> x. if x = cockpit then [''Charly''] 
            else (if x = door then [''Bob''] 
                  else (if x = cabin then [''Alice''] else [])))
        ex_creds ex_locs"

fixes agid_graph :: "igraph"
defines agid_graph_def: "agid_graph \<equiv>  Lgraph
      {(cockpit, door),(door,cabin)}
      (\<lambda> x. if x = cockpit then [''Charly''] 
            else (if x = door then [] 
                  else (if x = cabin then [''Bob'', ''Alice''] else [])))
      ex_creds ex_locs"
  
fixes local_policies :: "[igraph,  location] \<Rightarrow> apolicy set"
defines local_policies_def: "local_policies G \<equiv>  
   (\<lambda> y. if y = cockpit then
             {(\<lambda> x. (? n. (n @\<^bsub>G\<^esub> cockpit) \<and> Actor n = x), {put}),
              (\<lambda> x. (? n. (n @\<^bsub>G\<^esub> cabin) \<and> Actor n = x \<and> has G (x, ''PIN'')
                    \<and> isin G door ''norm''),{move})
             }
         else (if y = door then {(\<lambda> x. True, {move}),
                       (\<lambda> x. (? n. (n @\<^bsub>G\<^esub> cockpit) \<and> Actor n = x), {put})}
               else (if y = cabin then {(\<lambda> x. True, {move})} 
                     else {})))"

(* changed policy in which always two have to be in cockpit to do a put,
   simply change the above to two actors *)
fixes local_policies_four_eyes :: "[igraph, location] \<Rightarrow> apolicy set"
defines local_policies_four_eyes_def: "local_policies_four_eyes G \<equiv>  
   (\<lambda> y. if y = cockpit then
             {(\<lambda> x.  (? n. (n @\<^bsub>G\<^esub> cockpit) \<and> Actor n = x) \<and>
                     2 \<le> length(agra G y) \<and> (\<forall> h \<in> set(agra G y). h \<in> airplane_actors), {put}),
              (\<lambda> x. (? n. (n @\<^bsub>G\<^esub> cabin) \<and> Actor n = x \<and> has G (x, ''PIN'') \<and> 
                           isin G door ''norm'' ),{move})
             }
         else (if y = door then 
              {(\<lambda> x.  ((? n. (n @\<^bsub>G\<^esub> cockpit) \<and> Actor n = x) \<and> 3 \<le> length(agra G cockpit)), {move})}
               else (if y = cabin then 
                     {(\<lambda> x. ((? n. (n @\<^bsub>G\<^esub> door) \<and> Actor n = x)\<and> 3 \<le> length(agra G cockpit)), {move})} 
                           else {})))"

fixes Airplane_scenario :: "infrastructure" (structure)
defines Airplane_scenario_def:
"Airplane_scenario \<equiv> Infrastructure ex_graph local_policies"

fixes Airplane_in_danger :: "infrastructure"
defines Airplane_in_danger_def:
"Airplane_in_danger \<equiv> Infrastructure aid_graph local_policies"

(* Intermediate step where pilot left cockpit but door still in
   norm position *)
fixes Airplane_getting_in_danger0 :: "infrastructure"
defines Airplane_getting_in_danger0_def:
"Airplane_getting_in_danger0 \<equiv> Infrastructure aid_graph0 local_policies"

fixes Airplane_getting_in_danger :: "infrastructure"
defines Airplane_getting_in_danger_def:
"Airplane_getting_in_danger \<equiv> Infrastructure agid_graph local_policies"

(* For state transition we need Kripke structure *)
fixes Air_states
defines Air_states_def: "Air_states \<equiv> { I. Airplane_scenario \<rightarrow>\<^sub>n* I }"

fixes Air_Kripke
defines "Air_Kripke \<equiv> Kripke Air_states {Airplane_scenario}"

(* Two-person policy excludes attack *)
fixes Airplane_not_in_danger :: "infrastructure"
defines Airplane_not_in_danger_def:
"Airplane_not_in_danger \<equiv> Infrastructure aid_graph local_policies_four_eyes"

fixes Airplane_not_in_danger_init :: "infrastructure"
defines Airplane_not_in_danger_init_def:
"Airplane_not_in_danger_init \<equiv> Infrastructure ex_graph local_policies_four_eyes"

(* Kripke for two-person variant*)
fixes Air_tp_states
defines Air_tp_states_def: "Air_tp_states \<equiv> { I. Airplane_not_in_danger_init \<rightarrow>\<^sub>n* I }"

fixes Air_tp_Kripke
defines "Air_tp_Kripke \<equiv> Kripke Air_tp_states {Airplane_not_in_danger_init}"

(* Safety *)
fixes Safety :: "[infrastructure, identity] \<Rightarrow> bool"
defines Safety_def: "Safety I a \<equiv> a \<in> airplane_actors  
                       \<longrightarrow> (enables I cockpit (Actor a) move)"
(* Security *)
fixes Security :: "[infrastructure, identity] \<Rightarrow> bool"
defines Security_def: "Security I a \<equiv>  (isin (graphI I) door ''locked'') 
                       \<longrightarrow> \<not>(enables I cockpit (Actor a) move)"

fixes foe_control :: "[location, action, infrastructure kripke] \<Rightarrow> bool"
defines foe_control_def: "foe_control l c K \<equiv>  
   (\<forall> I:: infrastructure \<in> states K. (\<exists> x :: identity. 
        (x @\<^bsub>graphI I\<^esub> l) \<and> Actor x \<noteq> Actor ''Eve'')
             \<longrightarrow> \<not>(enables I l (Actor ''Eve'') c))"

fixes astate:: "identity \<Rightarrow> actor_state"
defines astate_def: "astate x \<equiv>  (case x of 
           ''Eve'' \<Rightarrow> Actor_state depressed {revenge, peer_recognition}
          | _ \<Rightarrow> Actor_state happy {})"

assumes Eve_precipitating_event: "tipping_point (astate ''Eve'')"
assumes Insider_Eve: "Insider ''Eve'' {''Charly''} astate"
assumes cockpit_foe_control: "foe_control cockpit put Air_tp_Kripke"

begin

lemma "Actor ''Eve'' = Actor ''Charly''"
  using Eve_precipitating_event Insider_Eve Insider_def UasI_def by blast

subsection \<open>Insider Attack, Safety, and Security\<close>
text \<open>Above, we first stage the insider attack and introduce
basic definitions of safety and security for the airplane scenario.
To invoke the insider within an application of the Isabelle
Insider framework, we assume in the locale @{text \<open>airplane\<close>} 
as a locale assumption with @{text \<open>assumes\<close>} that the tipping point 
has been reached for @{text \<open>Eve\<close>} which manifests itself in her
@{text \<open>actor_state\<close>} assigned by the locale function @{text \<open>astate\<close>}.

In addition, we state that she is an insider being able to
impersonate @{text \<open>Charly\<close>} by locally assuming the @{text \<open>Insider\<close>}
predicate. This predicate allows an insider to impersonate a set of
other actor identities; in this case the set is singleton.

Next, the process of analysis uses this assumption as well as the definitions
of the previous section to prove security properties interactively as theorems
in Isabelle. We use the strong insider assumption here up front to provide a 
first sanity check on the model by validating the infrastructure
for the ``normal'' case. We prove that the global policy holds for the 
pilot Bob.
\<close>
lemma ex_inv: "global_policy Airplane_scenario ''Bob''"
by (simp add: Airplane_scenario_def global_policy_def airplane_actors_def)


text \<open>We can prove the same theorem for @{text \<open>Charly\<close>} who 
is the copilot in the scenario (omitting the proof and accompanying
Isabelle commands).\<close>
lemma ex_inv2: "global_policy Airplane_scenario ''Charly''"
by (simp add: Airplane_scenario_def global_policy_def airplane_actors_def)

text \<open>But @{text \<open>Eve\<close>} is an insider and is able to impersonate @{text \<open>Charly\<close>}.
She will ignore the global policy.
This insider threat can now be formalized as an invalidation 
of the global company policy for @{text \<open>''Eve''\<close>} in the following ``attack'' theorem 
named @{text \<open>ex_inv3\<close>}:\<close>
lemma ex_inv3: "\<not>global_policy Airplane_scenario ''Eve''"
proof (simp add: Airplane_scenario_def global_policy_def, rule conjI)
  show "''Eve'' \<notin> airplane_actors" by (simp add: airplane_actors_def)
next show 
  "enables (Infrastructure ex_graph local_policies) cockpit (Actor ''Eve'') put"
  proof -
    have a: "Actor ''Charly'' = Actor ''Eve''" 
      by (insert Insider_Eve, unfold Insider_def, (drule mp), 
          rule Eve_precipitating_event, simp add: UasI_def)
    show ?thesis   
      by (insert a, simp add: Airplane_scenario_def enables_def ex_creds_def local_policies_def ex_graph_def,
         insert Insider_Eve, unfold Insider_def, (drule mp), rule Eve_precipitating_event, 
         simp add: UasI_def, rule_tac x = "''Charly''" in exI, simp add: cockpit_def atI_def)
  qed
qed

text\<open>Safety and security are sometimes introduced in textbooks as complementary
properties, see, e.g., \cite{gol:08}. Safety expresses that humans and goods should 
be protected from negative effects caused by machines while security is the inverse
direction: machines (computers) should be protected from malicious humans.
Similarly, the following descriptions of safety and security in the airplane
scenario also illustrate this complementarity: 
one says that the door must stay closed to the outside; the other that there must 
be a possibility to open it from the outside.
\begin{description}
\item[\it Safety:] if the actors in the cockpit are out of action, there must be a possibility
to get into the cockpit from the cabin, and 
\item[\it Security:] \hspace*{2ex}if the actors in the 
cockpit fear an attack from the cabin, they can lock the door.
\end{description}
In the formal translation of these properties into HOL, this complementarity
manifests itself even more clearly: the conclusions of the two formalizations of 
the properties are negations of each other.
Safety is quite concisely described by stating that airplane actors can move 
into the cockpit.

We show Safety for @{text \<open>Airplane_scenario\<close>}.\<close>
lemma Safety: "Safety Airplane_scenario (''Alice'')"
proof -
  show "Safety Airplane_scenario ''Alice''"
    by (simp add: Airplane_scenario_def Safety_def enables_def ex_creds_def 
                local_policies_def ex_graph_def cockpit_def, rule impI,
        rule_tac x = "''Alice''" in exI, simp add: atI_def cabin_def ex_locs_def door_def,
        rule conjI, simp add: has_def credentials_def, simp add: isin_def credentials_def)
qed

text \<open>Security can also be defined in a simple manner as the property that
no actor can move into the cockpit if the door is on lock. 

We show Security for @{text \<open>Airplane_scenario\<close>}. We need some lemmas first that
use the injectivity of the @{text \<open>is_in\<close>} predicate to infer that the lock and the 
norm states of the door must be actually different. \<close>
lemma inj_lem: "\<lbrakk> inj f; x \<noteq> y \<rbrakk> \<Longrightarrow> f x \<noteq> f y"
by (simp add: inj_eq)

lemma inj_on_lem: "\<lbrakk> inj_on f A; x \<noteq> y; x\<in> A; y \<in> A \<rbrakk> \<Longrightarrow> f x \<noteq> f y"
by (simp add: inj_on_def, blast)

lemma inj_lemma': "inj_on (isin ex_graph door) {''locked'',''norm''} "
  by (unfold inj_on_def ex_graph_def isin_def, simp, unfold ex_locs_def, simp)

lemma inj_lemma'': "inj_on (isin aid_graph door) {''locked'',''norm''} "
 by (unfold inj_on_def aid_graph_def isin_def, simp, unfold ex_locs'_def, simp)

lemma locl_lemma2: "isin ex_graph door ''norm'' \<noteq> isin ex_graph door ''locked''"
by (rule_tac A = "{''locked'',''norm''}" and f = "isin ex_graph door" in inj_on_lem,
        rule inj_lemma', simp+)

lemma locl_lemma3: "isin ex_graph door ''norm'' = (\<not> isin ex_graph door ''locked'')"
by (insert locl_lemma2, blast)

lemma locl_lemma2a: "isin aid_graph door ''norm'' \<noteq> isin aid_graph door ''locked''"
by (rule_tac A = "{''locked'',''norm''}" and f = "isin aid_graph door" in inj_on_lem,
       rule inj_lemma'', simp+)

lemma locl_lemma3a: "isin aid_graph door ''norm'' = (\<not> isin aid_graph door ''locked'')"
by (insert locl_lemma2a, blast)

text \<open>In general, we could prove safety for any airplane actor who is in the cabin
for this state of the infrastructure.

In a slightly more complex proof, we can prove security for any
other identity which can be simply instantiated to @{text \<open>''Bob''\<close>}, for example.\<close>
lemma Security: "Security Airplane_scenario s"
  by (simp add: Airplane_scenario_def Security_def enables_def local_policies_def ex_locs_def locl_lemma3)
 
lemma Security_problem: "Security Airplane_scenario ''Bob''"
by (rule Security)

text \<open>We show that pilot can get out of cockpit\<close>
lemma pilot_can_leave_cockpit: "(enables Airplane_scenario cabin (Actor ''Bob'') move)"
  by (simp add: Airplane_scenario_def Security_def ex_creds_def ex_graph_def enables_def 
                local_policies_def ex_locs_def, simp add: cockpit_def cabin_def door_def)

text \<open>We show that in @{text \<open>Airplane_in_danger\<close>}, the copilot can still do @{text \<open>put\<close>} and therefore
     can @{text \<open>put\<close>} position to ground.\<close>
lemma ex_inv4: "\<not>global_policy Airplane_in_danger (''Eve'')"
proof (simp add: Airplane_in_danger_def global_policy_def, rule conjI)
  show "''Eve'' \<notin> airplane_actors" by (simp add: airplane_actors_def)
next show "enables (Infrastructure aid_graph local_policies) cockpit (Actor ''Eve'') put"
  proof -
    have a: "Actor ''Charly'' = Actor ''Eve''" 
      by (insert Insider_Eve, unfold Insider_def, (drule mp), 
          rule Eve_precipitating_event, simp add: UasI_def)
    show ?thesis
     apply (insert a, erule subst)
     by (simp add: enables_def local_policies_def cockpit_def aid_graph_def atI_def)
 qed
qed

lemma Safety_in_danger:
  fixes s
  assumes "s \<in> airplane_actors" 
  shows   "\<not>(Safety Airplane_in_danger s)"
proof (simp add: Airplane_in_danger_def Safety_def enables_def assms)
  show "\<forall>x::(actor \<Rightarrow> bool) \<times> action set\<in>local_policies aid_graph cockpit.
       \<not> (case x of (p::actor \<Rightarrow> bool, e::action set) \<Rightarrow> move \<in> e \<and> p (Actor s))"
    by ( simp add: local_policies_def aid_graph_def ex_locs'_def isin_def)
qed

lemma Security_problem': " \<not>(enables Airplane_in_danger cockpit (Actor ''Bob'') move) "
proof (simp add: Airplane_in_danger_def Security_def enables_def local_policies_def 
       ex_locs_def locl_lemma3a, rule impI)
  assume "has aid_graph (Actor ''Bob'', ''PIN'')"
  show "(\<forall>n::char list.
        Actor n = Actor ''Bob'' \<longrightarrow> (n @\<^bsub>aid_graph\<^esub> cabin) \<longrightarrow> isin aid_graph door ''locked'')"
by (simp add: aid_graph_def isin_def ex_locs'_def)
qed

text \<open>We show that with the four eyes rule in @{text \<open>Airplane_not_in_danger\<close>} Eve cannot 
   crash the plane, i.e. cannot put position to ground.\<close>
lemma ex_inv5: "a \<in> airplane_actors \<longrightarrow> global_policy Airplane_not_in_danger a"
by (simp add: Airplane_not_in_danger_def global_policy_def)

lemma ex_inv6: "global_policy Airplane_not_in_danger a"
proof (simp add: Airplane_not_in_danger_def global_policy_def, rule impI)
  assume "a \<notin> airplane_actors"
  show "\<not> enables (Infrastructure aid_graph local_policies_four_eyes) cockpit (Actor a) put"
by (simp add: aid_graph_def ex_locs'_def enables_def local_policies_four_eyes_def)
qed

text \<open>The simple formalizations of safety and security enable 
proofs only over a particular state of the airplane infrastructure at a time 
but this is not enough since the general airplane structure is subject
to state changes.
For a general verification, we need to prove that the properties of interest
are preserved under potential changes. Since the airplane infrastructure
permits, for example, that actors move about inside the airplane, we need to 
verify safety and security properties in a dynamic setting.
After all, the insider attack on Germanwings Flight 9525 appeared when the pilot had moved out of the
cockpit. Furthermore, we want to redefine the policy into the two-person
policy and examine whether safety and security are improved.
For these reasons, we next apply the general Kripke structure mechanism
introduced initially to the airplane scenario.\<close>

section \<open>Analysis of Safety and Security Properties\<close>
text \<open>For the analysis of security, we need to ask whether the
infrastructure state @{text \<open>Airplane_in_danger\<close>} is reachable
via the state transition relation from the initial state.
It is. We can prove the theorem @{text \<open>step_all_r\<close>} in the locale @{text \<open>airplane\<close>}.

As the name of this theorem suggests it is the result of lining up a 
sequence of steps that lead from the initial @{text \<open>Airplane_scenario\<close>}
to that @{text \<open>Airplane_in_danger\<close>} state (for the state definitions see the
above defintion section of the locale).
In fact there are three steps via two intermediary infrastructure
states @{text \<open>Airplane_getting_in_danger0\<close>} and 
@{text \<open>Airplane_getting_in_danger\<close>}.
The former encodes the state where @{text \<open>Bob\<close>} has moved to the cabin and
the latter encodes the successor state in which additionally the lock state 
has changed to @{text \<open>locked\<close>}. \<close>

lemma step0:  "Airplane_scenario \<rightarrow>\<^sub>n Airplane_getting_in_danger0"
proof (rule_tac l = cockpit and l' = door and a = "''Bob''" in  move, rule refl)
  show "''Bob'' @\<^bsub>graphI Airplane_scenario\<^esub> cockpit"
  by (simp add: Airplane_scenario_def atI_def ex_graph_def)
next show "cockpit \<in> nodes (graphI Airplane_scenario)"
    by (simp add: ex_graph_def Airplane_scenario_def nodes_def, blast)+
next show "door \<in> nodes (graphI Airplane_scenario)"
   by (simp add: actors_graph_def door_def cockpit_def nodes_def cabin_def,
       rule_tac x = "Location 2" in exI,     
       simp add: Airplane_scenario_def ex_graph_def cockpit_def door_def)
next show "''Bob'' \<in> actors_graph (graphI Airplane_scenario)"
    by (simp add: actors_graph_def Airplane_scenario_def nodes_def ex_graph_def, blast)
next show "enables Airplane_scenario door (Actor ''Bob'') move"
   by (simp add: Airplane_scenario_def enables_def local_policies_def ex_creds_def door_def cockpit_def)
next show "Airplane_getting_in_danger0 =
    Infrastructure (move_graph_a ''Bob'' cockpit door (graphI Airplane_scenario))
     (delta Airplane_scenario)"
  proof -
    have a: "(move_graph_a ''Bob'' cockpit door (graphI Airplane_scenario)) = aid_graph0" 
      by (simp add: move_graph_a_def door_def cockpit_def Airplane_scenario_def 
          aid_graph0_def ex_graph_def, rule ext, simp add: cabin_def door_def)
    show ?thesis
      by (unfold Airplane_getting_in_danger0_def, insert a, erule ssubst, 
          simp add: Airplane_scenario_def)
  qed
qed
    
lemma step1:  "Airplane_getting_in_danger0 \<rightarrow>\<^sub>n Airplane_getting_in_danger"
proof (rule_tac l = door and l' = cabin and a = "''Bob''" in  move, rule refl)
  show "''Bob'' @\<^bsub>graphI Airplane_getting_in_danger0\<^esub> door"
  by (simp add: Airplane_getting_in_danger0_def atI_def aid_graph0_def door_def cockpit_def)
next show "door \<in> nodes (graphI Airplane_getting_in_danger0)"
    by (simp add: aid_graph0_def Airplane_getting_in_danger0_def nodes_def, blast)+
next show "cabin \<in> nodes (graphI Airplane_getting_in_danger0)"
    by (simp add: actors_graph_def door_def cockpit_def nodes_def cabin_def,
    rule_tac x = "Location 1" in exI,    
    simp add: Airplane_getting_in_danger0_def aid_graph0_def cockpit_def door_def cabin_def)
next show "''Bob'' \<in> actors_graph (graphI Airplane_getting_in_danger0)"
   by (simp add: actors_graph_def door_def cockpit_def nodes_def cabin_def 
                  Airplane_getting_in_danger0_def aid_graph0_def, blast)
next show "enables Airplane_getting_in_danger0 cabin (Actor ''Bob'') move"
   by (simp add: Airplane_getting_in_danger0_def enables_def local_policies_def ex_creds_def door_def 
                cockpit_def cabin_def)
next show "Airplane_getting_in_danger =
    Infrastructure (move_graph_a ''Bob'' door cabin (graphI Airplane_getting_in_danger0))
     (delta Airplane_getting_in_danger0)"
    by (unfold Airplane_getting_in_danger_def,
        simp add: Airplane_getting_in_danger0_def agid_graph_def aid_graph0_def 
                  move_graph_a_def door_def cockpit_def cabin_def, rule ext,
        simp add: cabin_def door_def)
qed

lemma step2: "Airplane_getting_in_danger \<rightarrow>\<^sub>n Airplane_in_danger"
proof (rule_tac l = door and a = "''Charly''" and z = "''locked''" in  put_remote, rule refl)
  show "enables Airplane_getting_in_danger door (Actor ''Charly'') put"
   by (simp add: enables_def local_policies_def ex_creds_def door_def cockpit_def,
       unfold Airplane_getting_in_danger_def,
       simp add: local_policies_def cockpit_def cabin_def door_def,
       rule_tac x = "''Charly''" in exI, rule conjI,
       simp add: atI_def agid_graph_def door_def cockpit_def, rule refl) 
next show "Airplane_in_danger =
    Infrastructure
     (Lgraph (gra (graphI Airplane_getting_in_danger)) (agra (graphI Airplane_getting_in_danger))
       (cgra (graphI Airplane_getting_in_danger))
       ((lgra (graphI Airplane_getting_in_danger))(door := [''locked''])))
     (delta Airplane_getting_in_danger)"
    by (unfold Airplane_in_danger_def, simp add: aid_graph_def agid_graph_def 
               ex_locs'_def ex_locs_def Airplane_getting_in_danger_def, force)
qed

lemma step0r: "Airplane_scenario \<rightarrow>\<^sub>n* Airplane_getting_in_danger0"
  by (simp add: state_transition_in_refl_def, insert step0, auto)

lemma step1r: "Airplane_getting_in_danger0 \<rightarrow>\<^sub>n* Airplane_getting_in_danger"
  by (simp add: state_transition_in_refl_def, insert step1, auto)

lemma step2r: "Airplane_getting_in_danger \<rightarrow>\<^sub>n* Airplane_in_danger"
  by (simp add: state_transition_in_refl_def, insert step2, auto)
  
theorem step_allr:  "Airplane_scenario \<rightarrow>\<^sub>n* Airplane_in_danger"
  by (insert step0r step1r step2r, simp add: state_transition_in_refl_def)

text \<open>Using the formalization of CTL over Kripke structures introduced initiall, 
we can now transform the attack sequence represented implicitly by the above theorem 
@{text \<open>step_allr\<close>} into a temporal logic statement. This attack theorem states that 
there is a path from the initial state of the Kripke structure @{text \<open>Air_Kripke\<close>}
on which eventually the global policy is violated by the attacker.\<close>
theorem aid_attack: "Air_Kripke \<turnstile> EF ({x. \<not> global_policy x ''Eve''})"
proof (simp add: check_def Air_Kripke_def, rule conjI)
  show "Airplane_scenario \<in> Air_states" 
    by (simp add: Air_states_def state_transition_in_refl_def)
next show "Airplane_scenario \<in> EF {x::infrastructure. \<not> global_policy x ''Eve''}"
  by (rule EF_lem2b, subst EF_lem000, rule EX_lem0r, subst EF_lem000, rule EX_step,
     unfold state_transition_infra_def, rule step0, rule EX_lem0r,
     rule_tac y = "Airplane_getting_in_danger" in EX_step,
     unfold state_transition_infra_def, rule step1, subst EF_lem000, rule EX_lem0l,
     rule_tac y = "Airplane_in_danger" in EX_step, unfold state_transition_infra_def,
     rule step2, rule CollectI, rule ex_inv4)
qed
text \<open>The proof uses the underlying formalization of CTL and the lemmas that
are provided to evaluate the @{text \<open>EF\<close>} statement on the Kripke structure.
However, the attack sequence is already provided by the previous theorem.
So the proof just consists in supplying the step lemmas for each step and
finally proving that for the state at the end of the attack path, i.e.,
for @{text \<open>Airplane_in_danger\<close>}, the global policy is violated.
This proof corresponds precisely to the proof of the attack theorem 
@{text \<open>ex_inv3\<close>}. It is not surprising that the security attack is 
possible in the reachable state @{text \<open>Airplane_in_danger\<close>} when it
was already possible in the initial state. However, this statement is 
not satisfactory since the model does not take into account whether 
the copilot is on his own when he launches the attack.
This is the purpose of the two-person rule which we want to investigate in
more detail in this paper. Therefore, we next address how to add the 
two-person role to the model.\<close>

subsection \<open>Introduce Two-Person Rule\<close>
text \<open>To express the rule that two authorized
personnel must be present at all times in the cockpit, we have define a second set of
local policies @{text \<open>local_policies_four_eyes\<close>} (see above). It realizes the two-person 
constraint requesting that the number of actors at the location @{text \<open>cockpit\<close>} in the
graph @{text \<open>G\<close>} given as input must be at least two to enable actors at
the location to perform the action @{text \<open>put\<close>}.  Formally, we can express 
this here as @{text \<open>2 \<le> length(agra G cockpit)\<close>} since we have all of
arithmetic available (remember @{text \<open>agra G y\<close>} is the list of 
actors at location @{text \<open>y\<close>} in @{text \<open>G\<close>}.

Note that the two-person rule requires three people to be at the cockpit
before one of them can leave. This is formalized as a condition on the 
@{text \<open>move\<close>} action of location @{text \<open>door\<close>}. A move of an actor
@{text \<open>x\<close>} in the cockpit to @{text \<open>door\<close>} is only allowed if three people are in 
the cockpit.
Practically, it enforces a person, say Alice to first enter 
the cockpit before the pilot Bob can leave.
However, this condition is necessary to guarantee that the two-person
requirement for @{text \<open>cockpit\<close>} is sustained by the dynamic changes to 
the infrastructure state caused by actors' moves.
A move to location @{text \<open>cabin\<close>} is only allowed from @{text \<open>door\<close>}
so no additional condition is necessary here.

What is stated informally above seems intuitive and quite easy to believe.
However, comparing to the earlier formalization of this two-person rule \cite{kk:16}, 
it appears that the earlier version did not have the additional condition on the 
action @{text \<open>move\<close>} to @{text \<open>door\<close>}. 
One may argue that in the earlier version the authors did not consider
this because they had neither state transitions, Kripke structures, nor CTL
to consider dynamic changes. However, in the current paper this additional
side condition only occurred to us when we tried to prove the
invariant @{text \<open>two_person_invariant1\<close>}
which is needed in the subsequent security proof.

The proof of @{text \<open>two_person_invariant1\<close>} requires an induction over the state 
transition relation
starting in the infrastructure state @{text \<open>Airplane_not_in_danger_init\<close>} (see above)
with Charly and Bob in the cockpit and the two-person policy in place.

The corresponding Kripke structure of all states originating in this 
infrastructure state is defined as @{text \<open>Air_tp_Kripke\<close>}.
Within the induction for the proof of the above @{text \<open>two_person_inv1\<close>}, 
a preservation lemma is required that proves that if the condition 

@{text \<open>2 \<le> length (agra (graphI I) cockpit)\<close>}

holds for @{text \<open>I\<close>} and @{text \<open>I \<rightarrow> I'\<close>} then it also 
holds for @{text \<open>I'\<close>}. The preservation lemma is actually trickier to
prove. It uses a case analysis over all the transition rules for each action. 
The rules for @{text \<open>put\<close>} and @{text \<open>get\<close>} are easy to prove for the user 
as they are solved by the simplification tactic automatically. The case for
action @{text \<open>move\<close>} is the difficult case. Here we actually need to 
use the precondition of the policy for location @{text \<open>door\<close>} in 
order to prove that the two-person invariant is preserved
by an actor moving out of the cockpit.
In this case, we need for example, invariants like the following
lemma @{text \<open>actors_unique_loc_aid_step\<close>} that shows that in any 
infrastructure state originating
from @{text \<open>Airplane_not_in_danger_init\<close>} actors only ever appear
in one location and they do not appear more than once in a location --
which is expressed in the predicate @{text \<open>nodup\<close>} (see above).\<close>

text \<open>Invariant: actors cannot be at two places at the same time\<close>
lemma  actors_unique_loc_base: 
  assumes "I \<rightarrow>\<^sub>n I'"
      and "(\<forall> l l'. (a @\<^bsub>graphI I\<^esub> l) \<and> (a @\<^bsub>graphI I\<^esub> l') \<longrightarrow> l = l')\<and>
           (\<forall> l. nodup a (agra (graphI I) l))"
    shows "(\<forall> l l'. (a @\<^bsub>graphI I'\<^esub> l) \<and> (a @\<^bsub>graphI I'\<^esub> l')  \<longrightarrow> l = l') \<and>
           (\<forall> l. nodup a (agra (graphI I') l))"
proof (rule state_transition_in.cases, rule assms(1))
  show "\<And>(G::igraph) (Ia::infrastructure) (aa::char list) (l::location) (a'::char list) (z::char list)
       I'a::infrastructure.
       I = Ia \<Longrightarrow>
       I' = I'a \<Longrightarrow>
       G = graphI Ia \<Longrightarrow>
       aa @\<^bsub>G\<^esub> l \<Longrightarrow>
       a' @\<^bsub>G\<^esub> l \<Longrightarrow>
       has G (Actor aa, z) \<Longrightarrow>
       enables Ia l (Actor aa) get \<Longrightarrow>
       I'a =
       Infrastructure
        (Lgraph (gra G) (agra G)
          ((cgra G)(Actor a' := (z # fst (cgra G (Actor a')), snd (cgra G (Actor a'))))) (lgra G))
        (delta Ia) \<Longrightarrow>
       (\<forall>(l::location) l'::location. (a @\<^bsub>graphI I'\<^esub> l) \<and> (a @\<^bsub>graphI I'\<^esub> l') \<longrightarrow> l = l') \<and>
       (\<forall>l::location. nodup a (agra (graphI I') l))" using assms
    by (simp add: atI_def)
next fix G Ia aa l I'a z
  assume a0: "I = Ia" and a1: "I' = I'a" and a2: "G = graphI Ia" and a3: "aa @\<^bsub>G\<^esub> l"
     and a4: "enables Ia l (Actor aa) put" 
     and a5: "I'a = Infrastructure (Lgraph (gra G) (agra G) (cgra G) ((lgra G)(l := [z]))) (delta Ia)"
  show "(\<forall>(l::location) l'::location. (a @\<^bsub>graphI I'\<^esub> l) \<and> (a @\<^bsub>graphI I'\<^esub> l') \<longrightarrow> l = l') \<and>
       (\<forall>l::location. nodup a (agra (graphI I') l))"using assms
    by (simp add: a0 a1 a2 a3 a4 a5 atI_def)
next show "\<And>(G::igraph) (Ia::infrastructure) (l::location) (aa::char list) (I'a::infrastructure)
       z::char list.
       I = Ia \<Longrightarrow>
       I' = I'a \<Longrightarrow>
       G = graphI Ia \<Longrightarrow>
       enables Ia l (Actor aa) put \<Longrightarrow>
       I'a = Infrastructure (Lgraph (gra G) (agra G) (cgra G) ((lgra G)(l := [z]))) (delta Ia) \<Longrightarrow>
       (\<forall>(l::location) l'::location. (a @\<^bsub>graphI I'\<^esub> l) \<and> (a @\<^bsub>graphI I'\<^esub> l') \<longrightarrow> l = l') \<and>
       (\<forall>l::location. nodup a (agra (graphI I') l))"
    by (clarify, simp add: assms atI_def)
next show "\<And>(G::igraph) (Ia::infrastructure) (aa::char list) (l::location) (l'::location)
       I'a::infrastructure.
       I = Ia \<Longrightarrow>
       I' = I'a \<Longrightarrow>
       G = graphI Ia \<Longrightarrow>
       aa @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> nodes G \<Longrightarrow>
       l' \<in> nodes G \<Longrightarrow>
       aa \<in> actors_graph (graphI Ia) \<Longrightarrow>
       enables Ia l' (Actor aa) move \<Longrightarrow>
       I'a = Infrastructure (move_graph_a aa l l' (graphI Ia)) (delta Ia) \<Longrightarrow>
       (\<forall>(l::location) l'::location. (a @\<^bsub>graphI I'\<^esub> l) \<and> (a @\<^bsub>graphI I'\<^esub> l') \<longrightarrow> l = l') \<and>
       (\<forall>l::location. nodup a (agra (graphI I') l))"
  proof (simp add: move_graph_a_def,rule conjI, clarify, rule conjI, clarify, rule conjI, clarify)
    show "\<And>(G::igraph) (Ia::infrastructure) (aa::char list) (l::location) (l'::location)
       (I'a::infrastructure) (la::location) l'a::location.
       I' =
       Infrastructure
        (Lgraph (gra (graphI I))
          (if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
           then (agra (graphI I))(l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
           else agra (graphI I))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I) \<Longrightarrow>
       a @\<^bsub>graphI I\<^esub> l \<Longrightarrow>
       l \<in> nodes (graphI I) \<Longrightarrow>
       l' \<in> nodes (graphI I) \<Longrightarrow>
       a \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I l' (Actor a) move \<Longrightarrow>
       a \<in> set (agra (graphI I) l) \<Longrightarrow>
       a \<notin> set (agra (graphI I) l') \<Longrightarrow>
       a @\<^bsub>Lgraph (gra (graphI I))
            ((agra (graphI I))(l := del a (agra (graphI I) l), l' := a # agra (graphI I) l'))
            (cgra (graphI I)) (lgra (graphI I))\<^esub> la \<Longrightarrow>
       a @\<^bsub>Lgraph (gra (graphI I))
            ((agra (graphI I))(l := del a (agra (graphI I) l), l' := a # agra (graphI I) l'))
            (cgra (graphI I)) (lgra (graphI I))\<^esub> l'a \<Longrightarrow>
       la = l'a"
      apply (case_tac "la \<noteq> l' \<and> la \<noteq> l \<and> l'a \<noteq> l' \<and> l'a \<noteq> l")
       apply (simp add: atI_def)
       apply (subgoal_tac "la = l' \<or> la = l \<or> l'a = l' \<or> l'a = l")
      prefer 2
      using assms(2) atI_def apply blast
      apply blast
      by (metis agra.simps assms(2) atI_def del_nodup fun_upd_apply)
  next show "\<And>(G::igraph) (Ia::infrastructure) (aa::char list) (l::location) (l'::location)
       I'a::infrastructure.
       I' =
       Infrastructure
        (Lgraph (gra (graphI I))
          (if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
           then (agra (graphI I))(l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
           else agra (graphI I))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I) \<Longrightarrow>
       a @\<^bsub>graphI I\<^esub> l \<Longrightarrow>
       l \<in> nodes (graphI I) \<Longrightarrow>
       l' \<in> nodes (graphI I) \<Longrightarrow>
       a \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I l' (Actor a) move \<Longrightarrow>
       a \<in> set (agra (graphI I) l) \<Longrightarrow>
       a \<notin> set (agra (graphI I) l') \<Longrightarrow>
       \<forall>la::location.
          (la = l \<longrightarrow> l \<noteq> l' \<longrightarrow> nodup a (del a (agra (graphI I) l))) \<and>
          (la \<noteq> l \<longrightarrow> la \<noteq> l' \<longrightarrow> nodup a (agra (graphI I) la))"
      by (simp add: assms(2) nodup_down)
  next show "\<And>(G::igraph) (Ia::infrastructure) (aa::char list) (l::location) (l'::location)
       I'a::infrastructure.
       I' =
       Infrastructure
        (Lgraph (gra (graphI I))
          (if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
           then (agra (graphI I))(l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
           else agra (graphI I))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I) \<Longrightarrow>
       a @\<^bsub>graphI I\<^esub> l \<Longrightarrow>
       l \<in> nodes (graphI I) \<Longrightarrow>
       l' \<in> nodes (graphI I) \<Longrightarrow>
       a \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I l' (Actor a) move \<Longrightarrow>
       (a \<in> set (agra (graphI I) l) \<longrightarrow> a \<in> set (agra (graphI I) l')) \<longrightarrow>
       (\<forall>(l::location) l'::location.
           (a @\<^bsub>Lgraph (gra (graphI I)) (agra (graphI I)) (cgra (graphI I)) (lgra (graphI I))\<^esub> l) \<and>
           (a @\<^bsub>Lgraph (gra (graphI I)) (agra (graphI I)) (cgra (graphI I)) (lgra (graphI I))\<^esub> l') \<longrightarrow>
           l = l') \<and>
       (\<forall>l::location. nodup a (agra (graphI I) l))"
      by (simp add: assms(2) atI_def)
  next show "\<And>(G::igraph) (Ia::infrastructure) (aa::char list) (l::location) (l'::location)
       I'a::infrastructure.
       I = Ia \<Longrightarrow>
       I' =
       Infrastructure
        (Lgraph (gra (graphI Ia))
          (if aa \<in> set (agra (graphI Ia) l) \<and> aa \<notin> set (agra (graphI Ia) l')
           then (agra (graphI Ia))(l := del aa (agra (graphI Ia) l), l' := aa # agra (graphI Ia) l')
           else agra (graphI Ia))
          (cgra (graphI Ia)) (lgra (graphI Ia)))
        (delta Ia) \<Longrightarrow>
       G = graphI Ia \<Longrightarrow>
       aa @\<^bsub>graphI Ia\<^esub> l \<Longrightarrow>
       l \<in> nodes (graphI Ia) \<Longrightarrow>
       l' \<in> nodes (graphI Ia) \<Longrightarrow>
       aa \<in> actors_graph (graphI Ia) \<Longrightarrow>
       enables Ia l' (Actor aa) move \<Longrightarrow>
       I'a =
       Infrastructure
        (Lgraph (gra (graphI Ia))
          (if aa \<in> set (agra (graphI Ia) l) \<and> aa \<notin> set (agra (graphI Ia) l')
           then (agra (graphI Ia))(l := del aa (agra (graphI Ia) l), l' := aa # agra (graphI Ia) l')
           else agra (graphI Ia))
          (cgra (graphI Ia)) (lgra (graphI Ia)))
        (delta Ia) \<Longrightarrow>
       aa \<noteq> a \<longrightarrow>
       (aa \<in> set (agra (graphI Ia) l) \<and> aa \<notin> set (agra (graphI Ia) l') \<longrightarrow>
        (\<forall>(la::location) l'a::location.
            (a @\<^bsub>Lgraph (gra (graphI Ia))
                 ((agra (graphI Ia))
                  (l := del aa (agra (graphI Ia) l), l' := aa # agra (graphI Ia) l'))
                 (cgra (graphI Ia)) (lgra (graphI Ia))\<^esub> la) \<and>
            (a @\<^bsub>Lgraph (gra (graphI Ia))
                 ((agra (graphI Ia))
                  (l := del aa (agra (graphI Ia) l), l' := aa # agra (graphI Ia) l'))
                 (cgra (graphI Ia)) (lgra (graphI Ia))\<^esub> l'a) \<longrightarrow>
            la = l'a) \<and>
        (\<forall>la::location.
            (la = l \<longrightarrow>
             (l = l' \<longrightarrow> nodup a (agra (graphI Ia) l')) \<and>
             (l \<noteq> l' \<longrightarrow> nodup a (del aa (agra (graphI Ia) l)))) \<and>
            (la \<noteq> l \<longrightarrow>
             (la = l' \<longrightarrow> nodup a (agra (graphI Ia) l')) \<and>
             (la \<noteq> l' \<longrightarrow> nodup a (agra (graphI Ia) la))))) \<and>
       ((aa \<in> set (agra (graphI Ia) l) \<longrightarrow> aa \<in> set (agra (graphI Ia) l')) \<longrightarrow>
        (\<forall>(l::location) l'::location.
            (a @\<^bsub>Lgraph (gra (graphI Ia)) (agra (graphI Ia)) (cgra (graphI Ia))
                 (lgra (graphI Ia))\<^esub> l) \<and>
            (a @\<^bsub>Lgraph (gra (graphI Ia)) (agra (graphI Ia)) (cgra (graphI Ia))
                 (lgra (graphI Ia))\<^esub> l') \<longrightarrow>
            l = l') \<and>
        (\<forall>l::location. nodup a (agra (graphI Ia) l)))"
    proof (clarify, simp add: atI_def,rule conjI,clarify,rule conjI,clarify,rule conjI,
           clarify,rule conjI,clarify,simp,clarify,rule conjI,(rule impI)+)
      show "\<And>(aa::char list) (l::location) (l'::location) l'a::location.
       I' =
       Infrastructure
        (Lgraph (gra (graphI I))
          ((agra (graphI I))(l := del aa (agra (graphI I) l), l' := aa # agra (graphI I) l'))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I) \<Longrightarrow>
       aa \<in> set (agra (graphI I) l) \<Longrightarrow>
       l \<in> nodes (graphI I) \<Longrightarrow>
       l' \<in> nodes (graphI I) \<Longrightarrow>
       aa \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I l' (Actor aa) move \<Longrightarrow>
       aa \<noteq> a \<Longrightarrow>
       aa \<notin> set (agra (graphI I) l') \<Longrightarrow>
       l \<noteq> l' \<Longrightarrow>
       l'a \<noteq> l \<Longrightarrow>
       l'a = l' \<Longrightarrow> a \<in> set (del aa (agra (graphI I) l)) \<Longrightarrow> a \<notin> set (agra (graphI I) l')"
        by (meson assms(2) atI_def del_notin_down)
    next show "\<And>(aa::char list) (l::location) (l'::location) l'a::location.
       I' =
       Infrastructure
        (Lgraph (gra (graphI I))
          ((agra (graphI I))(l := del aa (agra (graphI I) l), l' := aa # agra (graphI I) l'))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I) \<Longrightarrow>
       aa \<in> set (agra (graphI I) l) \<Longrightarrow>
       l \<in> nodes (graphI I) \<Longrightarrow>
       l' \<in> nodes (graphI I) \<Longrightarrow>
       aa \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I l' (Actor aa) move \<Longrightarrow>
       aa \<noteq> a \<Longrightarrow>
       aa \<notin> set (agra (graphI I) l') \<Longrightarrow>
       l \<noteq> l' \<Longrightarrow>
       l'a \<noteq> l \<Longrightarrow>
       l'a \<noteq> l' \<longrightarrow> a \<in> set (del aa (agra (graphI I) l)) \<longrightarrow> a \<notin> set (agra (graphI I) l'a)"
        by (meson assms(2) atI_def del_notin_down)
    next show "\<And>(aa::char list) (l::location) (l'::location) la::location.
       I' =
       Infrastructure
        (Lgraph (gra (graphI I))
          (if aa \<notin> set (agra (graphI I) l')
           then (agra (graphI I))(l := del aa (agra (graphI I) l), l' := aa # agra (graphI I) l')
           else agra (graphI I))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I) \<Longrightarrow>
       aa \<in> set (agra (graphI I) l) \<Longrightarrow>
       l \<in> nodes (graphI I) \<Longrightarrow>
       l' \<in> nodes (graphI I) \<Longrightarrow>
       aa \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I l' (Actor aa) move \<Longrightarrow>
       aa \<noteq> a \<Longrightarrow>
       aa \<notin> set (agra (graphI I) l') \<Longrightarrow>
       la \<noteq> l \<longrightarrow>
       (la = l' \<longrightarrow>
        (\<forall>l'a::location.
            (l'a = l \<longrightarrow>
             l \<noteq> l' \<longrightarrow> a \<in> set (agra (graphI I) l') \<longrightarrow> a \<notin> set (del aa (agra (graphI I) l))) \<and>
            (l'a \<noteq> l \<longrightarrow>
             l'a \<noteq> l' \<longrightarrow> a \<in> set (agra (graphI I) l') \<longrightarrow> a \<notin> set (agra (graphI I) l'a)))) \<and>
       (la \<noteq> l' \<longrightarrow>
        (\<forall>l'a::location.
            (l'a = l \<longrightarrow>
             (l = l' \<longrightarrow> a \<in> set (agra (graphI I) la) \<longrightarrow> a \<notin> set (agra (graphI I) l')) \<and>
             (l \<noteq> l' \<longrightarrow> a \<in> set (agra (graphI I) la) \<longrightarrow> a \<notin> set (del aa (agra (graphI I) l)))) \<and>
            (l'a \<noteq> l \<longrightarrow>
             (l'a = l' \<longrightarrow> a \<in> set (agra (graphI I) la) \<longrightarrow> a \<notin> set (agra (graphI I) l')) \<and>
             (l'a \<noteq> l' \<longrightarrow>
              a \<in> set (agra (graphI I) la) \<and> a \<in> set (agra (graphI I) l'a) \<longrightarrow> la = l'a))))"
        by (meson assms(2) atI_def del_notin_down)
    next show "\<And>(aa::char list) (l::location) l'::location.
       I' =
       Infrastructure
        (Lgraph (gra (graphI I))
          (if aa \<notin> set (agra (graphI I) l')
           then (agra (graphI I))(l := del aa (agra (graphI I) l), l' := aa # agra (graphI I) l')
           else agra (graphI I))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I) \<Longrightarrow>
       aa \<in> set (agra (graphI I) l) \<Longrightarrow>
       l \<in> nodes (graphI I) \<Longrightarrow>
       l' \<in> nodes (graphI I) \<Longrightarrow>
       aa \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I l' (Actor aa) move \<Longrightarrow>
       aa \<noteq> a \<Longrightarrow>
       aa \<notin> set (agra (graphI I) l') \<Longrightarrow>
       \<forall>la::location.
          (la = l \<longrightarrow>
           (l = l' \<longrightarrow> nodup a (agra (graphI I) l')) \<and>
           (l \<noteq> l' \<longrightarrow> nodup a (del aa (agra (graphI I) l)))) \<and>
          (la \<noteq> l \<longrightarrow>
           (la = l' \<longrightarrow> nodup a (agra (graphI I) l')) \<and> (la \<noteq> l' \<longrightarrow> nodup a (agra (graphI I) la)))"
        by (simp add: assms(2) nodup_down_notin)
    next show "\<And>(aa::char list) (l::location) l'::location.
       I' =
       Infrastructure
        (Lgraph (gra (graphI I))
          (if aa \<notin> set (agra (graphI I) l')
           then (agra (graphI I))(l := del aa (agra (graphI I) l), l' := aa # agra (graphI I) l')
           else agra (graphI I))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I) \<Longrightarrow>
       aa \<in> set (agra (graphI I) l) \<Longrightarrow>
       l \<in> nodes (graphI I) \<Longrightarrow>
       l' \<in> nodes (graphI I) \<Longrightarrow>
       aa \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I l' (Actor aa) move \<Longrightarrow>
       aa \<noteq> a \<Longrightarrow>
       aa \<in> set (agra (graphI I) l') \<longrightarrow>
       (\<forall>(l::location) l'::location.
           a \<in> set (agra (graphI I) l) \<and> a \<in> set (agra (graphI I) l') \<longrightarrow> l = l') \<and>
       (\<forall>l::location. nodup a (agra (graphI I) l))"
        using assms(2) atI_def by blast
    qed
  qed
qed   

lemma actors_unique_loc_step: 
  assumes "(I, I') \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*" 
      and "\<forall> a. (\<forall> l l'. (a @\<^bsub>graphI I\<^esub> l) \<and> (a @\<^bsub>graphI I\<^esub> l') \<longrightarrow> l = l')\<and>
          (\<forall> l. nodup a (agra (graphI I) l))" 
    shows   "\<forall> a. (\<forall> l l'. (a @\<^bsub>graphI I'\<^esub> l) \<and> (a @\<^bsub>graphI I'\<^esub> l')  \<longrightarrow> l = l') \<and>
          (\<forall> l. nodup a (agra (graphI I') l))"
proof -
  have ind: "(\<forall> a. (\<forall> l l'. (a @\<^bsub>graphI I\<^esub> l) \<and> (a @\<^bsub>graphI I\<^esub> l') \<longrightarrow> l = l')\<and>
          (\<forall> l. nodup a (agra (graphI I) l))) \<longrightarrow>
       (\<forall> a. (\<forall> l l'. (a @\<^bsub>graphI I'\<^esub> l) \<and> (a @\<^bsub>graphI I'\<^esub> l')  \<longrightarrow> l = l') \<and>
          (\<forall> l. nodup a (agra (graphI I') l)))"
  proof (insert assms(1), erule rtrancl.induct)
    show "\<And>a::infrastructure.
       (\<forall>aa::char list.
           (\<forall>(l::location) l'::location. (aa @\<^bsub>graphI a\<^esub> l) \<and> (aa @\<^bsub>graphI a\<^esub> l') \<longrightarrow> l = l') \<and>
           (\<forall>l::location. nodup aa (agra (graphI a) l))) \<longrightarrow>
       (\<forall>aa::char list.
           (\<forall>(l::location) l'::location. (aa @\<^bsub>graphI a\<^esub> l) \<and> (aa @\<^bsub>graphI a\<^esub> l') \<longrightarrow> l = l') \<and>
           (\<forall>l::location. nodup aa (agra (graphI a) l)))" by simp
  next show "\<And>(a::infrastructure) (b::infrastructure) (c::infrastructure).
       (a, b) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       (\<forall>aa::char list.
           (\<forall>(l::location) (l'::location). (aa @\<^bsub>graphI a\<^esub> l) \<and> (aa @\<^bsub>graphI a\<^esub> l') \<longrightarrow> l = l') \<and>
           (\<forall>l::location. nodup aa (agra (graphI a) l))) \<longrightarrow>
       (\<forall>a::char list.
           (\<forall>(l::location) (l'::location). (a @\<^bsub>graphI b\<^esub> l) \<and> (a @\<^bsub>graphI b\<^esub> l') \<longrightarrow> l = l') \<and>
           (\<forall>l::location. nodup a (agra (graphI b) l))) \<Longrightarrow>
       (b, c) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
       (\<forall>aa::char list.
           (\<forall>(l::location) l'::location. (aa @\<^bsub>graphI a\<^esub> l) \<and> (aa @\<^bsub>graphI a\<^esub> l') \<longrightarrow> l = l') \<and>
           (\<forall>l::location. nodup aa (agra (graphI a) l))) \<longrightarrow>
       (\<forall>a::char list.
           (\<forall>(l::location) l'::location. (a @\<^bsub>graphI c\<^esub> l) \<and> (a @\<^bsub>graphI c\<^esub> l') \<longrightarrow> l = l') \<and>
           (\<forall>l::location. nodup a (agra (graphI c) l)))"
      by (rule impI, rule allI, rule actors_unique_loc_base, drule CollectD, 
             simp,erule impE, assumption, erule spec)   
  qed
  show ?thesis 
  by (insert ind, insert assms(2), simp)
qed

lemma actors_unique_loc_aid_base:"
 \<forall> a. (\<forall> l l'. (a @\<^bsub>graphI Airplane_not_in_danger_init\<^esub> l) \<and> 
               (a @\<^bsub>graphI Airplane_not_in_danger_init\<^esub> l') \<longrightarrow> l = l')\<and>
         (\<forall> l. nodup a (agra (graphI Airplane_not_in_danger_init) l))"  
proof (simp add: Airplane_not_in_danger_init_def ex_graph_def, clarify, rule conjI, clarify,
      rule conjI, clarify, rule impI, (rule allI)+, rule impI, simp add: atI_def)
  show "\<And>(l::location) l'::location.
       ''Charly''
       \<in> set (if l = cockpit then [''Bob'', ''Charly'']
               else if l = door then [] else if l = cabin then [''Alice''] else []) \<and>
       ''Charly''
       \<in> set (if l' = cockpit then [''Bob'', ''Charly'']
               else if l' = door then [] else if l' = cabin then [''Alice''] else []) \<Longrightarrow>
       l = l'"
  by (case_tac "l = l'", assumption, rule FalseE, case_tac "l = cockpit \<or> l = door \<or> l = cabin",
      erule disjE, simp, case_tac "l' = door \<or> l' = cabin", erule disjE, simp, 
      simp add: cabin_def door_def, simp, erule disjE, simp add: door_def cockpit_def, 
      simp add: cabin_def door_def cockpit_def, simp)
next show "\<And>a::char list.
       ''Charly'' \<noteq> a \<longrightarrow>
       (\<forall>(l::location) l'::location.
           (a @\<^bsub>Lgraph {(cockpit, door), (door, cabin)}
                (\<lambda>x::location.
                    if x = cockpit then [''Bob'', ''Charly'']
                    else if x = door then [] else if x = cabin then [''Alice''] else [])
                ex_creds ex_locs\<^esub> l) \<and>
           (a @\<^bsub>Lgraph {(cockpit, door), (door, cabin)}
                (\<lambda>x::location.
                    if x = cockpit then [''Bob'', ''Charly'']
                    else if x = door then [] else if x = cabin then [''Alice''] else [])
                ex_creds ex_locs\<^esub> l') \<longrightarrow>
           l = l')"
  by (clarify, simp add: atI_def, case_tac "l = l'", assumption, rule FalseE,
      case_tac "l = cockpit \<or> l = door \<or> l = cabin", erule disjE, simp,
      case_tac "l' = door \<or> l' = cabin", erule disjE, simp, simp add: cabin_def door_def,
      simp, erule disjE, simp add: door_def cockpit_def, case_tac "l = cockpit",
      simp add: cabin_def cockpit_def, simp add: cabin_def door_def, case_tac "l' = cockpit",
      simp, simp add: cabin_def, case_tac "l' = door", simp, simp add: cabin_def, simp)
qed

lemma actors_unique_loc_aid_step: 
"(Airplane_not_in_danger_init, I)\<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*
 \<Longrightarrow>     \<forall> a. (\<forall> l l'. (a @\<^bsub>graphI I\<^esub> l) \<and> (a @\<^bsub>graphI I\<^esub> l') \<longrightarrow> l = l')\<and>
         (\<forall> l. nodup a (agra (graphI I) l))"  
  by (erule actors_unique_loc_step, rule actors_unique_loc_aid_base)
    
text \<open>Using the state transition, Kripke structure and CTL, we can now
   also express (and prove!) unreachability properties which enable to 
   formally verify security properties for specific policies, like the two-person
   rule.\<close>
lemma Anid_airplane_actors: "actors_graph (graphI Airplane_not_in_danger_init) = airplane_actors"
proof (simp add: Airplane_not_in_danger_init_def ex_graph_def actors_graph_def nodes_def 
                 airplane_actors_def, rule equalityI)
  show "{x::char list.
     \<exists>y::location.
        (y = door \<longrightarrow>
         (door = cockpit \<longrightarrow>
          (\<exists>y::location. y = cockpit \<or> y = cabin \<or> y = cockpit \<or> y = cockpit \<and> cockpit = cabin) \<and>
          (x = ''Bob'' \<or> x = ''Charly'')) \<and>
         door = cockpit) \<and>
        (y \<noteq> door \<longrightarrow>
         (y = cockpit \<longrightarrow>
          (\<exists>y::location.
              y = door \<or>
              cockpit = door \<and> y = cabin \<or>
              y = cockpit \<and> cockpit = door \<or> y = door \<and> cockpit = cabin) \<and>
          (x = ''Bob'' \<or> x = ''Charly'')) \<and>
         (y \<noteq> cockpit \<longrightarrow> y = cabin \<and> x = ''Alice'' \<and> y = cabin))}
    \<subseteq> {''Bob'', ''Charly'', ''Alice''}"
  by (rule subsetI, drule CollectD, erule exE, (erule conjE)+,
      simp add: door_def cockpit_def cabin_def, (erule conjE)+, force)
next show "{''Bob'', ''Charly'', ''Alice''}
    \<subseteq> {x::char list.
        \<exists>y::location.
           (y = door \<longrightarrow>
            (door = cockpit \<longrightarrow>
             (\<exists>y::location.
                 y = cockpit \<or> y = cabin \<or> y = cockpit \<or> y = cockpit \<and> cockpit = cabin) \<and>
             (x = ''Bob'' \<or> x = ''Charly'')) \<and>
            door = cockpit) \<and>
           (y \<noteq> door \<longrightarrow>
            (y = cockpit \<longrightarrow>
             (\<exists>y::location.
                 y = door \<or>
                 cockpit = door \<and> y = cabin \<or>
                 y = cockpit \<and> cockpit = door \<or> y = door \<and> cockpit = cabin) \<and>
             (x = ''Bob'' \<or> x = ''Charly'')) \<and>
            (y \<noteq> cockpit \<longrightarrow> y = cabin \<and> x = ''Alice'' \<and> y = cabin))}"
  by (rule subsetI, rule CollectI, simp add: door_def cockpit_def cabin_def,
      case_tac "x = ''Bob''", force, case_tac "x = ''Charly''", force,
      subgoal_tac "x = ''Alice''", force, simp)    
qed

lemma all_airplane_actors: "(Airplane_not_in_danger_init, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
              \<Longrightarrow> actors_graph(graphI y) = airplane_actors"
  by (insert Anid_airplane_actors, erule subst, rule sym, erule same_actors)
      
lemma actors_at_loc_in_graph: "\<lbrakk> l \<in> nodes(graphI I); a  @\<^bsub>graphI I\<^esub> l\<rbrakk>
                                \<Longrightarrow> a \<in> actors_graph (graphI I)"
  by (simp add: atI_def actors_graph_def, rule exI, rule conjI)

lemma not_en_get_Apnid: 
  assumes "(Airplane_not_in_danger_init,y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*" 
  shows   "~(enables y l (Actor a) get)"
proof -
  have "delta y = delta(Airplane_not_in_danger_init)" 
  by (insert assms, rule sym, erule_tac init_state_policy)
  with assms show ?thesis 
    by (simp add: Airplane_not_in_danger_init_def enables_def local_policies_four_eyes_def)    
qed
 
lemma Apnid_tsp_test: "~(enables Airplane_not_in_danger_init cockpit (Actor ''Alice'') get)"    
  by (simp add: Airplane_not_in_danger_init_def ex_creds_def enables_def 
                local_policies_four_eyes_def cabin_def door_def cockpit_def 
                ex_graph_def ex_locs_def)

lemma Apnid_tsp_test_gen: "~(enables Airplane_not_in_danger_init l (Actor a) get)"    
  by (simp add: Airplane_not_in_danger_init_def ex_creds_def enables_def 
                local_policies_four_eyes_def cabin_def door_def cockpit_def 
                ex_graph_def ex_locs_def)

lemma test_graph_atI: "''Bob'' @\<^bsub>graphI Airplane_not_in_danger_init\<^esub> cockpit" 
  by (simp add: Airplane_not_in_danger_init_def ex_graph_def atI_def)  

lemma "\<not> (foe_control cockpit put Air_tp_Kripke)"
  oops
(*
  by (smt Airplane_not_in_danger_init_def Airplane_scenario_def Eve_precipitating_event Insider_Eve 
      Insider_def UasI_def char.inject ex_inv3 foe_control_def global_policy_def graphI.simps 
      list.inject singletonI test_graph_atI) *)
  
  text \<open>The following invariant shows that the number of staff in the cockpit is never below 2.\<close>
lemma two_person_inv: 
      "z \<rightarrow>\<^sub>n z'
     \<Longrightarrow> (2::nat) \<le> length (agra (graphI z) cockpit)
     \<Longrightarrow> nodes(graphI z) = nodes(graphI Airplane_not_in_danger_init)
     \<Longrightarrow> delta(Airplane_not_in_danger_init) = delta z
     \<Longrightarrow> (Airplane_not_in_danger_init,z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*
    \<Longrightarrow> (2::nat) \<le> length (agra (graphI z') cockpit)" 
proof (erule state_transition_in.cases, simp, subgoal_tac "l' = cabin \<or> l' = door \<or> l' = cockpit", erule disjE, simp)
  show \<open>\<And>G I a l l' I'.
       2 \<le> length (agra (graphI I) cockpit) \<Longrightarrow>
       nodes (graphI I) = nodes (graphI Airplane_not_in_danger_init) \<Longrightarrow>
       delta Airplane_not_in_danger_init = delta I \<Longrightarrow>
       (Airplane_not_in_danger_init, I) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = Infrastructure (move_graph_a a l cabin (graphI I)) (delta I) \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>graphI I\<^esub> l \<Longrightarrow>
       l \<in> nodes (graphI Airplane_not_in_danger_init) \<Longrightarrow>
       cabin \<in> nodes (graphI Airplane_not_in_danger_init) \<Longrightarrow>
       a \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I cabin (Actor a) move \<Longrightarrow>
       I' = Infrastructure (move_graph_a a l cabin (graphI I)) (delta I) \<Longrightarrow>
       l' = cabin \<Longrightarrow> 2 \<le> length (agra (move_graph_a a l cabin (graphI I)) cockpit)\<close>
       apply (subgoal_tac "delta I = local_policies_four_eyes")
       apply (simp add: enables_def local_policies_four_eyes_def)
  proof -
    fix G :: igraph and I :: infrastructure and a :: "char list" and l :: location and l' :: location and I' :: infrastructure
    assume a1: "2 \<le> length (agra (graphI I) cockpit)"
    assume a2: "\<exists>x\<in>if cabin = cockpit then {(\<lambda>x. (\<exists>n. n @\<^bsub>graphI I\<^esub> cockpit \<and> Actor n = x) \<and> 2 \<le> length (agra (graphI I) cabin) \<and> (\<forall>h\<in>set (agra (graphI I) cabin). h \<in> airplane_actors), {put}), (\<lambda>x. \<exists>n. n @\<^bsub>graphI I\<^esub> cabin \<and> Actor n = x \<and> has (graphI I) (x, ''PIN'') \<and> isin (graphI I) door ''norm'', {move})} else if cabin = door then {(\<lambda>x. (\<exists>n. n @\<^bsub>graphI I\<^esub> cockpit \<and> Actor n = x) \<and> 3 \<le> length (agra (graphI I) cockpit), {move})} else if cabin = cabin then {(\<lambda>x. (\<exists>n. n @\<^bsub>graphI I\<^esub> door \<and> Actor n = x) \<and> 3 \<le> length (agra (graphI I) cockpit), {move})} else {}. case x of (p, e) \<Rightarrow> move \<in> e \<and> p (Actor a)"
    have f3: "cabin \<noteq> cockpit"
      by (simp add: cabin_def cockpit_def)
  obtain pp :: "(actor \<Rightarrow> bool) \<times> action set" where
        f4: "pp \<in> (if cabin = cockpit then {(\<lambda>a. (\<exists>cs. cs @\<^bsub>graphI I\<^esub> cockpit \<and> Actor cs = a) \<and> 2 \<le> length (agra (graphI I) cabin) \<and> (\<forall>cs. cs \<in> set (agra (graphI I) cabin) \<longrightarrow> cs \<in> airplane_actors), {put}), (\<lambda>a. \<exists>cs. cs @\<^bsub>graphI I\<^esub> cabin \<and> Actor cs = a \<and> has (graphI I) (a, ''PIN'') \<and> isin (graphI I) door ''norm'', {move})} else if cabin = door then {(\<lambda>a. (\<exists>cs. cs @\<^bsub>graphI I\<^esub> cockpit \<and> Actor cs = a) \<and> 3 \<le> length (agra (graphI I) cockpit), {move})} else {(\<lambda>a. (\<exists>cs. cs @\<^bsub>graphI I\<^esub> door \<and> Actor cs = a) \<and> 3 \<le> length (agra (graphI I) cockpit), {move})}) \<and> (case pp of (p, A) \<Rightarrow> move \<in> A \<and> p (Actor a))"
    using a2 by meson
  then have f5: "pp = (\<lambda>a. (\<exists>cs. cs @\<^bsub>graphI I\<^esub> door \<and> Actor cs = a) \<and> 3 \<le> length (agra (graphI I) cockpit), {move}) \<longrightarrow> move \<in> {move} \<and> (\<exists>cs. cs @\<^bsub>graphI I\<^esub> door \<and> Actor cs = Actor a) \<and> 3 \<le> length (agra (graphI I) cockpit)"
    by blast
  { assume "\<not> (move \<in> {move} \<and> (\<exists>cs. cs @\<^bsub>graphI I\<^esub> cockpit \<and> Actor cs = Actor a) \<and> 3 \<le> length (agra (graphI I) cockpit))"
    then have "pp \<noteq> (\<lambda>a. (\<exists>cs. cs @\<^bsub>graphI I\<^esub> cockpit \<and> Actor cs = a) \<and> 3 \<le> length (agra (graphI I) cockpit), {move})"
      using f4 by blast
then have "3 \<le> length (agra (graphI I) cockpit)"
using f5 f4 f3 by (meson empty_iff insert_iff) }
  moreover
  { assume "(agra (graphI I)) (l := del a (agra (graphI I) l), cabin := a # agra (graphI I) cabin) \<noteq> agra (move_graph_a a l cabin (graphI I))"
    then have "a \<notin> set (agra (graphI I) l) \<or> a \<in> set (agra (graphI I) cabin)"
      using move_graph_a_def by force
    then have "2 \<le> length (agra (move_graph_a a l cabin (graphI I)) cockpit)"
      using a1 agra.simps move_graph_a_def by presburger }
  ultimately show "2 \<le> length (agra (move_graph_a a l cabin (graphI I)) cockpit)"
    using f3 a1 by (metis (no_types) del_sort fun_upd_apply numeral_2_eq_2 numeral_3_eq_3)
next show \<open>\<And>G I a l l' I'.
       2 \<le> length (agra (graphI I) cockpit) \<Longrightarrow>
       nodes (graphI I) = nodes (graphI Airplane_not_in_danger_init) \<Longrightarrow>
       delta Airplane_not_in_danger_init = delta I \<Longrightarrow>
       (Airplane_not_in_danger_init, I) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = Infrastructure (move_graph_a a l cabin (graphI I)) (delta I) \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>graphI I\<^esub> l \<Longrightarrow>
       l \<in> nodes (graphI Airplane_not_in_danger_init) \<Longrightarrow>
       cabin \<in> nodes (graphI Airplane_not_in_danger_init) \<Longrightarrow>
       a \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I cabin (Actor a) move \<Longrightarrow>
       I' = Infrastructure (move_graph_a a l cabin (graphI I)) (delta I) \<Longrightarrow>
       l' = cabin \<Longrightarrow> delta I = local_policies_four_eyes \<close>
    by (simp add: Airplane_not_in_danger_init_def) 
qed
next show \<open> \<And>G I a l l' I'.
       2 \<le> length (agra (graphI I) cockpit) \<Longrightarrow>
       nodes (graphI I) = nodes (graphI Airplane_not_in_danger_init) \<Longrightarrow>
       delta Airplane_not_in_danger_init = delta I \<Longrightarrow>
       (Airplane_not_in_danger_init, I) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = Infrastructure (move_graph_a a l l' (graphI I)) (delta I) \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>graphI I\<^esub> l \<Longrightarrow>
       l \<in> nodes (graphI Airplane_not_in_danger_init) \<Longrightarrow>
       l' \<in> nodes (graphI Airplane_not_in_danger_init) \<Longrightarrow>
       a \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I l' (Actor a) move \<Longrightarrow>
       I' = Infrastructure (move_graph_a a l l' (graphI I)) (delta I) \<Longrightarrow>
       l' = door \<or> l' = cockpit \<Longrightarrow> 2 \<le> length (agra (move_graph_a a l l' (graphI I)) cockpit)\<close>
     proof (erule disjE)
       show \<open>\<And>G I a l l' I'.
       2 \<le> length (agra (graphI I) cockpit) \<Longrightarrow>
       nodes (graphI I) = nodes (graphI Airplane_not_in_danger_init) \<Longrightarrow>
       delta Airplane_not_in_danger_init = delta I \<Longrightarrow>
       (Airplane_not_in_danger_init, I) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = Infrastructure (move_graph_a a l l' (graphI I)) (delta I) \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>graphI I\<^esub> l \<Longrightarrow>
       l \<in> nodes (graphI Airplane_not_in_danger_init) \<Longrightarrow>
       l' \<in> nodes (graphI Airplane_not_in_danger_init) \<Longrightarrow>
       a \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I l' (Actor a) move \<Longrightarrow>
       I' = Infrastructure (move_graph_a a l l' (graphI I)) (delta I) \<Longrightarrow>
       l' = door \<Longrightarrow> 2 \<le> length (agra (move_graph_a a l l' (graphI I)) cockpit)\<close>
       apply simp
       apply (subgoal_tac "delta I = local_policies_four_eyes")
        apply (simp add: enables_def local_policies_four_eyes_def)
        apply (erule bexE)
  apply (unfold Airplane_not_in_danger_init_def local_policies_four_eyes_def)
        apply simp
         apply (case_tac x)
        apply simp
  apply (subgoal_tac "(aa,b) \<in>
{(\<lambda>x. (\<exists>n. n @\<^bsub>graphI I\<^esub> cockpit \<and> Actor n = x) \<and>
                           3 \<le> length (agra (graphI I) cockpit),
                       {move})}")
         apply (subgoal_tac "3 \<le> length (agra (graphI I) cockpit)")
          prefer 2
  apply simp
          apply (simp add: move_graph_a_def)
  apply (metis (no_types, lifting) One_nat_def cockpit_def del_sort door_def location.inject numeral_2_eq_2 numeral_3_eq_3)
  apply (simp add: cabin_def cockpit_def door_def)
         by simp
next show \<open>\<And>G I a l l' I'.
       2 \<le> length (agra (graphI I) cockpit) \<Longrightarrow>
       nodes (graphI I) = nodes (graphI Airplane_not_in_danger_init) \<Longrightarrow>
       delta Airplane_not_in_danger_init = delta I \<Longrightarrow>
       (Airplane_not_in_danger_init, I) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = Infrastructure (move_graph_a a l l' (graphI I)) (delta I) \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>graphI I\<^esub> l \<Longrightarrow>
       l \<in> nodes (graphI Airplane_not_in_danger_init) \<Longrightarrow>
       l' \<in> nodes (graphI Airplane_not_in_danger_init) \<Longrightarrow>
       a \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I l' (Actor a) move \<Longrightarrow>
       I' = Infrastructure (move_graph_a a l l' (graphI I)) (delta I) \<Longrightarrow>
       l' = cockpit \<Longrightarrow> 2 \<le> length (agra (move_graph_a a l l' (graphI I)) cockpit)\<close>
         apply simp
         apply (subgoal_tac "delta I = local_policies_four_eyes")
        apply (simp add: enables_def local_policies_four_eyes_def)
    using move_graph_a_def apply auto[1]
    by (simp add: Airplane_not_in_danger_init_def)
qed
next show \<open>\<And>G I a l l' I'.
       2 \<le> length (agra (graphI I) cockpit) \<Longrightarrow>
       nodes (graphI I) = nodes (graphI Airplane_not_in_danger_init) \<Longrightarrow>
       delta Airplane_not_in_danger_init = delta I \<Longrightarrow>
       (Airplane_not_in_danger_init, I) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = Infrastructure (move_graph_a a l l' (graphI I)) (delta I) \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>graphI I\<^esub> l \<Longrightarrow>
       l \<in> nodes (graphI Airplane_not_in_danger_init) \<Longrightarrow>
       l' \<in> nodes (graphI Airplane_not_in_danger_init) \<Longrightarrow>
       a \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I l' (Actor a) move \<Longrightarrow>
       I' = Infrastructure (move_graph_a a l l' (graphI I)) (delta I) \<Longrightarrow> l' = cabin \<or> l' = door \<or> l' = cockpit\<close>
      by (metis (no_types, lifting) Airplane_not_in_danger_init_def all_not_in_conv delta.simps local_policies_four_eyes_def not_enableI2) 
  next show \<open>\<And>G I a l a' za I'.
       2 \<le> length (agra (graphI z) cockpit) \<Longrightarrow>
       nodes (graphI z) = nodes (graphI Airplane_not_in_danger_init) \<Longrightarrow>
       delta Airplane_not_in_danger_init = delta z \<Longrightarrow>
       (Airplane_not_in_danger_init, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       a' @\<^bsub>G\<^esub> l \<Longrightarrow>
       has G (Actor a, za) \<Longrightarrow>
       enables I l (Actor a) get \<Longrightarrow>
       I' =
       Infrastructure
        (Lgraph (gra G) (agra G) ((cgra G)(Actor a' := (za # fst (cgra G (Actor a')), snd (cgra G (Actor a'))))) (lgra G))
        (delta I) \<Longrightarrow>
       2 \<le> length (agra (graphI z') cockpit)\<close> by simp
  next show \<open>\<And>G I a l I' za.
       2 \<le> length (agra (graphI z) cockpit) \<Longrightarrow>
       nodes (graphI z) = nodes (graphI Airplane_not_in_danger_init) \<Longrightarrow>
       delta Airplane_not_in_danger_init = delta z \<Longrightarrow>
       (Airplane_not_in_danger_init, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       enables I l (Actor a) put \<Longrightarrow>
       I' = Infrastructure (Lgraph (gra G) (agra G) (cgra G) ((lgra G)(l := [za]))) (delta I) \<Longrightarrow>
       2 \<le> length (agra (graphI z') cockpit)\<close> by simp
  next show \<open>\<And>G I l a I' za.
       2 \<le> length (agra (graphI z) cockpit) \<Longrightarrow>
       nodes (graphI z) = nodes (graphI Airplane_not_in_danger_init) \<Longrightarrow>
       delta Airplane_not_in_danger_init = delta z \<Longrightarrow>
       (Airplane_not_in_danger_init, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       enables I l (Actor a) put \<Longrightarrow>
       I' = Infrastructure (Lgraph (gra G) (agra G) (cgra G) ((lgra G)(l := [za]))) (delta I) \<Longrightarrow>
       2 \<le> length (agra (graphI z') cockpit) \<close> by simp
  qed

lemma two_person_inv1:
  assumes "(Airplane_not_in_danger_init,z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*" 
  shows "(2::nat) \<le> length (agra (graphI z) cockpit)"  
proof (insert assms, erule rtrancl_induct)
  show "(2::nat) \<le> length (agra (graphI Airplane_not_in_danger_init) cockpit)"
  by (simp add: Airplane_not_in_danger_init_def ex_graph_def)    
next show "\<And>(y::infrastructure) z::infrastructure.
       (Airplane_not_in_danger_init, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       (y, z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
       (2::nat) \<le> length (agra (graphI y) cockpit) \<Longrightarrow> (2::nat) \<le> length (agra (graphI z) cockpit)"
  by (rule two_person_inv, simp, assumption, rule same_nodes, assumption, rule init_state_policy, assumption+)
qed

text \<open>The version of @{text \<open>two_person_inv\<close>} above, that we need, uses cardinality of lists of 
   actors rather than length of lists. Therefore, we first need some equivalences
   to then prove a restatement of @{text \<open>two_person_inv\<close>} in terms of sets.\<close>
text \<open>The proof idea is to show, since there are no duplicates in the list,
    @{text \<open>agra (graphI z) cockpit\<close>} therefore then 
    @{text \<open>card(set(agra (graphI z))) = length(agra (graphI z))\<close>}.\<close>
lemma nodup_card_insert: 
       "a \<notin> set l \<longrightarrow> card (insert a (set l)) = Suc (card (set l))"      
by auto
       
lemma no_dup_set_list_num_eq[rule_format]: 
    "(\<forall> a. nodup a l) \<longrightarrow> card (set l) = length l" 
  by (induct_tac l, simp, clarify, simp, erule impE, rule allI,
      drule_tac x = aa in spec, case_tac "a = aa", simp, erule nodup_notin, simp)
    
lemma two_person_set_inv: 
  assumes "(Airplane_not_in_danger_init,z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*" 
    shows "(2::nat) \<le> card (set (agra (graphI z) cockpit))"  
proof -
  have a: "card (set (agra (graphI z) cockpit)) = length(agra (graphI z) cockpit)"
   by (rule no_dup_set_list_num_eq, insert assms, drule actors_unique_loc_aid_step,
       drule_tac x = a in spec, erule conjE, erule_tac x = cockpit in spec)
  show ?thesis 
   by (insert a, erule ssubst, rule two_person_inv1, rule assms)
qed

subsection \<open>Revealing Necessary Assumption by Proof Failure\<close>
text \<open>We would expect -- and this has in fact been presented in \cite{kk:16} --
that the two-person rule guarantees the absence of the insider attack.

This is indeed a provable fact in the following state 
@{text \<open>Airplane_not_in_danger\<close>} defined similar to 
@{text \<open>Airplane_in_danger\<close>} from Section \ref{sec:airkripke} but
using the two-person policy.

@{text \<open>Airplane_not_in_danger \<equiv> Infrastructure aid_graph local_policies_four_eyes\<close>}

For this state, it can be proved  \cite{kk:16} that for any actor 
identity @{text \<open>a\<close>} the global policy holds.

@{text \<open>global_policy Airplane_not_in_danger a\<close>}

So, in the state @{text \<open>Airplane_not_in_danger\<close>} with the two-person rule,
there seems to be no danger. But this is precisely the scenario of the suicide 
attack! Charly is on his own in the cockpit -- why then does the two-person rule
imply he cannot act?

The state @{text \<open>Airplane_not_in_danger\<close>} defined in the earlier
formalization is mis-named: it uses the graph @{text \<open>aid_graph\<close>} to define
a state in which Bob has left the cockpit and the door is locked. 
Since there is only one actor present, the precondition of the local policy 
for @{text \<open>cockpit\<close>} is not met and hence the action @{text \<open>put\<close>} is not 
enabled for actor Charly.
Thus, the policy rule for cockpit is true because the precondition of this 
implication -- two people in the cockpit -- is false, 
and false implies anything: seemingly a disastrous failure of logic.

Fortunately, the above theorem has been derived in a preliminary model only \cite{kk:16} 
in which  state changes were not integrated yet and which has been precisely
for this reason recognized as inadequate.
Now, with state changes in the improved model, we have proved the two-person invariant 
@{text \<open>two_person_inv1\<close>}.
Thus, we can see that the system -- if started in @{text \<open>Airplane_not_in_danger_init\<close>} 
-- cannot reach the mis-named state @{text \<open>Airplane_not_in_danger\<close>} in which  Charly is 
on his own in the cockpit.

However, so far, no such general theorem has been proved yet. We 
only used CTL to discover attacks using @{text \<open>EF\<close>} formulas.
What we need for general security and what we consider next is to prove a global 
property with the temporal operator @{text \<open>AG\<close>} that proves that from a given 
initial state the global policy holds in all (@{text \<open>A\<close>}) states globally (@{text \<open>G\<close>}).

As we have seen in the previous section when looking at
the proof of @{text \<open>two_person_inv1\<close>}, it is not evident and trivial 
to prove that all state changes preserve security properties.
However, even this invariant does not suffice.

Even if the two-person rule is successfully enforced 
in a state, it is on its own still not sufficient. 
When we try to prove

@{text \<open>Air_tp_Kripke \<turnstile> AG \{x. global_policy x ''Eve''\}\<close>}

for the Kripke structure @{text \<open>Air_tp_Kripke\<close>} of all states
originating in @{text \<open>Airplane_not_in_danger_init\<close>},
we cannot succeed. In fact, in that Kripke structure
there are infrastructure states %of which we already know from previously
%proved lemmas that there 
where the insider attack is possible.
Despite the fact that we have stipulated the two-person rule as
part of the new policy and despite the fact that we can prove that
this policy is preserved by all state changes, the rule has no
consequence on the insider. Since Eve can impersonate the copilot
Charly, whether two people are in the cockpit or not, the attack can happen.

What we realize through this failed attempt to prove a global property
is that the policy formulation does not entail that the presence of
two people in itself actually disables an attacker.

This insight reveals a hidden assumption. Formal reasoning systems have the 
advantage that hidden assumptions must be made explicit. In human reasoning 
they occur when people assume a common understanding, which may or may not be 
actually the case. In the case of the rule above, its purpose may lead to an 
assumption that humans accept but which is not warranted.

We have used above a locale definition to encode this intentional understanding
of the two-person rule. The formula @{text \<open>foe_control\<close>} encodes for any 
action @{text \<open>c\<close>} at a location @{text \<open>l\<close>} that if there is an @{text \<open>Actor x\<close>}
that is not an insider, that is, is not impersonated by Eve, then the insider is
disabled for that action @{text \<open>c\<close>}.\<close>

subsection \<open>Proving Security in Refined Model\<close>
text \<open>Having identified the missing formulation of the intentional effects of
the two-person rule, we can now finally prove the general security property 
using the above locale definition.
We assume in the locale @{text \<open>airplane\<close>} an instance of @{text \<open>foe_control\<close>}
for the cockpit and the action @{text \<open>put\<close>}.

@{text \<open>assumes cockpit_foe_control: foe_control cockpit put\<close>}

With this assumption, we are now able to prove 

@{text \<open>theorem Four_eyes_no_danger: Air_tp_Kripke \<turnstile> AG {x. global_policy x ''Eve''}\<close>}

that is,
for all infrastructure states of the system @{text \<open>airplane\<close>} originating 
in state @{text \<open>Airplane_not_in_danger_init\<close>} Eve cannot put the 
airplane to the ground.

The proof uses as the key lemma @{text \<open>tp_imp_control\<close>} 
that within Kripke structure @{text \<open>Air_tp_Kripke\<close>} there is always someone in the cockpit 
who is not the insider. For this lemma, we first need some preparation.\<close>
lemma Pred_all_unique: "\<lbrakk> ? x. P x; (! x. P x \<longrightarrow> x = c)\<rbrakk> \<Longrightarrow> P c"
  by (case_tac "P c", assumption, erule exE, drule_tac x = x in spec,
      drule mp, assumption, erule subst) 
              
lemma Set_all_unique: "\<lbrakk> S \<noteq> {}; (\<forall> x \<in> S. x = c) \<rbrakk> \<Longrightarrow> c \<in> S"
  by (rule_tac P = "\<lambda> x. x \<in> S" in Pred_all_unique, force, simp)
    
lemma airplane_actors_inv0[rule_format]: 
    "\<forall> z z'. (\<forall>h::char list \<in> set (agra (graphI z) cockpit). h \<in> airplane_actors) \<and> 
          (Airplane_not_in_danger_init,z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<and>
            (z \<rightarrow>\<^sub>n z') \<longrightarrow>  (\<forall>h::char list\<in>set (agra (graphI z') cockpit). h \<in> airplane_actors)"     
proof (clarify, erule state_transition_in.cases)
  show " \<And>(z::infrastructure) (z'::infrastructure) (h::char list) (G::igraph) (I::infrastructure)
       (a::char list) (l::location) (a'::char list) (za::char list) I'::infrastructure.
       h \<in> set (agra (graphI z') cockpit) \<Longrightarrow>
       \<forall>h::char list\<in>set (agra (graphI z) cockpit). h \<in> airplane_actors \<Longrightarrow>
       (Airplane_not_in_danger_init, z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
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
       h \<in> airplane_actors"
    by simp
next show "\<And>(z::infrastructure) (z'::infrastructure) (h::char list) (G::igraph) (I::infrastructure)
       (a::char list) (l::location) (I'::infrastructure) za::char list.
       h \<in> set (agra (graphI z') cockpit) \<Longrightarrow>
       \<forall>h::char list\<in>set (agra (graphI z) cockpit). h \<in> airplane_actors \<Longrightarrow>
       (Airplane_not_in_danger_init, z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       enables I l (Actor a) put \<Longrightarrow>
       I' = Infrastructure (Lgraph (gra G) (agra G) (cgra G) ((lgra G)(l := [za]))) (delta I) \<Longrightarrow>
       h \<in> airplane_actors" 
    by simp
next show "\<And>(z::infrastructure) (z'::infrastructure) (h::char list) (G::igraph) (I::infrastructure)
       (l::location) (a::char list) (I'::infrastructure) za::char list.
       h \<in> set (agra (graphI z') cockpit) \<Longrightarrow>
       \<forall>h::char list\<in>set (agra (graphI z) cockpit). h \<in> airplane_actors \<Longrightarrow>
       (Airplane_not_in_danger_init, z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       enables I l (Actor a) put \<Longrightarrow>
       I' = Infrastructure (Lgraph (gra G) (agra G) (cgra G) ((lgra G)(l := [za]))) (delta I) \<Longrightarrow>
       h \<in> airplane_actors"
    by simp
next show "\<And>(z::infrastructure) (z'::infrastructure) (h::char list) (G::igraph) (I::infrastructure)
       (a::char list) (l::location) (l'::location) I'::infrastructure.
       h \<in> set (agra (graphI z') cockpit) \<Longrightarrow>
       \<forall>h::char list\<in>set (agra (graphI z) cockpit). h \<in> airplane_actors \<Longrightarrow>
       (Airplane_not_in_danger_init, z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> nodes G \<Longrightarrow>
       l' \<in> nodes G \<Longrightarrow>
       a \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I l' (Actor a) move \<Longrightarrow>
       I' = Infrastructure (move_graph_a a l l' (graphI I)) (delta I) \<Longrightarrow> h \<in> airplane_actors"
  proof (simp add: move_graph_a_def,
         case_tac "a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')")
    show "\<And>(z::infrastructure) (z'::infrastructure) (h::char list) (G::igraph) (I::infrastructure)
       (a::char list) (l::location) (l'::location) I'::infrastructure.
       h \<in> set ((if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
                  then (agra (graphI I))
                       (l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
                  else agra (graphI I))
                  cockpit) \<Longrightarrow>
       \<forall>h::char list\<in>set (agra (graphI I) cockpit). h \<in> airplane_actors \<Longrightarrow>
       (Airplane_not_in_danger_init, I) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       z = I \<Longrightarrow>
       z' =
       Infrastructure
        (Lgraph (gra (graphI I))
          (if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
           then (agra (graphI I))(l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
           else agra (graphI I))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I) \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>graphI I\<^esub> l \<Longrightarrow>
       l \<in> nodes (graphI I) \<Longrightarrow>
       l' \<in> nodes (graphI I) \<Longrightarrow>
       a \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I l' (Actor a) move \<Longrightarrow>
       I' =
       Infrastructure
        (Lgraph (gra (graphI I))
          (if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
           then (agra (graphI I))(l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
           else agra (graphI I))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I) \<Longrightarrow>
       \<not> (a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')) \<Longrightarrow> h \<in> airplane_actors"
      by simp
  next show "\<And>(z::infrastructure) (z'::infrastructure) (h::char list) (G::igraph) (I::infrastructure)
       (a::char list) (l::location) (l'::location) I'::infrastructure.
       h \<in> set ((if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
                  then (agra (graphI I))
                       (l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
                  else agra (graphI I))
                  cockpit) \<Longrightarrow>
       \<forall>h::char list\<in>set (agra (graphI I) cockpit). h \<in> airplane_actors \<Longrightarrow>
       (Airplane_not_in_danger_init, I) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       z = I \<Longrightarrow>
       z' =
       Infrastructure
        (Lgraph (gra (graphI I))
          (if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
           then (agra (graphI I))(l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
           else agra (graphI I))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I) \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>graphI I\<^esub> l \<Longrightarrow>
       l \<in> nodes (graphI I) \<Longrightarrow>
       l' \<in> nodes (graphI I) \<Longrightarrow>
       a \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I l' (Actor a) move \<Longrightarrow>
       I' =
       Infrastructure
        (Lgraph (gra (graphI I))
          (if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
           then (agra (graphI I))(l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
           else agra (graphI I))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I) \<Longrightarrow>
       a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l') \<Longrightarrow> h \<in> airplane_actors"
    proof (case_tac "l' = cockpit")
      show "\<And>(z::infrastructure) (z'::infrastructure) (h::char list) (G::igraph) (I::infrastructure)
       (a::char list) (l::location) (l'::location) I'::infrastructure.
       h \<in> set ((if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
                  then (agra (graphI I))
                       (l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
                  else agra (graphI I))
                  cockpit) \<Longrightarrow>
       \<forall>h::char list\<in>set (agra (graphI I) cockpit). h \<in> airplane_actors \<Longrightarrow>
       (Airplane_not_in_danger_init, I) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       z = I \<Longrightarrow>
       z' =
       Infrastructure
        (Lgraph (gra (graphI I))
          (if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
           then (agra (graphI I))(l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
           else agra (graphI I))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I) \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>graphI I\<^esub> l \<Longrightarrow>
       l \<in> nodes (graphI I) \<Longrightarrow>
       l' \<in> nodes (graphI I) \<Longrightarrow>
       a \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I l' (Actor a) move \<Longrightarrow>
       I' =
       Infrastructure
        (Lgraph (gra (graphI I))
          (if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
           then (agra (graphI I))(l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
           else agra (graphI I))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I) \<Longrightarrow>
       a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l') \<Longrightarrow>
       l' \<noteq> cockpit \<Longrightarrow> h \<in> airplane_actors"
      proof (case_tac "cockpit = l")
        show "\<And>(z::infrastructure) (z'::infrastructure) (h::char list) (G::igraph) (I::infrastructure)
             (a::char list) (l::location) (l'::location) I'::infrastructure.
              h \<in> set ((if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
                  then (agra (graphI I))
                       (l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
                  else agra (graphI I))
                  cockpit) \<Longrightarrow>
             \<forall>h::char list\<in>set (agra (graphI I) cockpit). h \<in> airplane_actors \<Longrightarrow>
             (Airplane_not_in_danger_init, I) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
             z = I \<Longrightarrow>
             z' =
             Infrastructure
                (Lgraph (gra (graphI I))
                  (if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
                  then (agra (graphI I))(l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
                  else agra (graphI I))
                  (cgra (graphI I)) (lgra (graphI I)))
                  (delta I) \<Longrightarrow>
                  G = graphI I \<Longrightarrow>
                  a @\<^bsub>graphI I\<^esub> l \<Longrightarrow>
                  l \<in> nodes (graphI I) \<Longrightarrow>
                  l' \<in> nodes (graphI I) \<Longrightarrow>
                  a \<in> actors_graph (graphI I) \<Longrightarrow>
                  enables I l' (Actor a) move \<Longrightarrow>
                  I' =
                  Infrastructure
                    (Lgraph (gra (graphI I))
                      (if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
                       then (agra (graphI I))(l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
                       else agra (graphI I))
                       (cgra (graphI I)) (lgra (graphI I)))
                       (delta I) \<Longrightarrow>
                  a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l') \<Longrightarrow>
                  l' \<noteq> cockpit \<Longrightarrow> cockpit \<noteq> l \<Longrightarrow> h \<in> airplane_actors"
          by simp
      next show " \<And>(z::infrastructure) (z'::infrastructure) (h::char list) (G::igraph) (I::infrastructure)
                    (a::char list) (l::location) (l'::location) I'::infrastructure.
                  h \<in> set ((if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
                  then (agra (graphI I))
                       (l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
                  else agra (graphI I))
                  cockpit) \<Longrightarrow>
                  \<forall>h::char list\<in>set (agra (graphI I) cockpit). h \<in> airplane_actors \<Longrightarrow>
                  (Airplane_not_in_danger_init, I) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
                  z = I \<Longrightarrow>
                  z' =
                  Infrastructure
                     (Lgraph (gra (graphI I))
                       (if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
                        then (agra (graphI I))(l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
                        else agra (graphI I))
                       (cgra (graphI I)) (lgra (graphI I)))
                       (delta I) \<Longrightarrow>
                  G = graphI I \<Longrightarrow>
                  a @\<^bsub>graphI I\<^esub> l \<Longrightarrow>
                  l \<in> nodes (graphI I) \<Longrightarrow>
                  l' \<in> nodes (graphI I) \<Longrightarrow>
                  a \<in> actors_graph (graphI I) \<Longrightarrow>
                  enables I l' (Actor a) move \<Longrightarrow>
                  I' =
                  Infrastructure
                    (Lgraph (gra (graphI I))
                      (if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
                       then (agra (graphI I))(l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
                       else agra (graphI I))
                             (cgra (graphI I)) (lgra (graphI I)))
                     (delta I) \<Longrightarrow>
                   a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l') \<Longrightarrow>
                  l' \<noteq> cockpit \<Longrightarrow> cockpit = l \<Longrightarrow> h \<in> airplane_actors"
          by (simp, erule bspec, erule del_up)
            qed
          next show "\<And>(z::infrastructure) (z'::infrastructure) (h::char list) (G::igraph) (I::infrastructure)
                       (a::char list) (l::location) (l'::location) I'::infrastructure.
                     h \<in> set ((if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
                               then (agra (graphI I))
                                    (l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
                               else agra (graphI I))
                              cockpit) \<Longrightarrow>
                       \<forall>h::char list\<in>set (agra (graphI I) cockpit). h \<in> airplane_actors \<Longrightarrow>
                     (Airplane_not_in_danger_init, I) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
                     z = I \<Longrightarrow>
                     z' =
                       Infrastructure
                         (Lgraph (gra (graphI I))
                           (if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
                            then (agra (graphI I))(l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
                            else agra (graphI I))
                            (cgra (graphI I)) (lgra (graphI I)))
                         (delta I) \<Longrightarrow>
                     G = graphI I \<Longrightarrow>
                     a @\<^bsub>graphI I\<^esub> l \<Longrightarrow>
                     l \<in> nodes (graphI I) \<Longrightarrow>
                     l' \<in> nodes (graphI I) \<Longrightarrow>
                     a \<in> actors_graph (graphI I) \<Longrightarrow>
                     enables I l' (Actor a) move \<Longrightarrow>
                     I' =
                        Infrastructure
                          (Lgraph (gra (graphI I))
                            (if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
                             then (agra (graphI I))(l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
                             else agra (graphI I))
                             (cgra (graphI I)) (lgra (graphI I)))
                          (delta I) \<Longrightarrow>
                     a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l') \<Longrightarrow>
                     l' = cockpit \<Longrightarrow> h \<in> airplane_actors"
            proof (simp, erule disjE)
              show "\<And>(z::infrastructure) (z'::infrastructure) (h::char list) (G::igraph) (I::infrastructure)
                     (a::char list) (l::location) (l'::location) I'::infrastructure.
                    \<forall>h::char list\<in>set (agra (graphI I) cockpit). h \<in> airplane_actors \<Longrightarrow>
                    (Airplane_not_in_danger_init, I) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
                    z = I \<Longrightarrow>
                    z' =
                     Infrastructure
                       (Lgraph (gra (graphI I))
                          ((agra (graphI I))
                           (l := del a (agra (graphI I) l), cockpit := a # agra (graphI I) cockpit))
                           (cgra (graphI I)) (lgra (graphI I)))
                       (delta I) \<Longrightarrow>
                    G = graphI I \<Longrightarrow>
                    a @\<^bsub>graphI I\<^esub> l \<Longrightarrow>
                    l \<in> nodes (graphI I) \<Longrightarrow>
                    cockpit \<in> nodes (graphI I) \<Longrightarrow>
                    a \<in> actors_graph (graphI I) \<Longrightarrow>
                    enables I cockpit (Actor a) move \<Longrightarrow>
                    I' =
                      Infrastructure
                        (Lgraph (gra (graphI I))
                          ((agra (graphI I))
                          (l := del a (agra (graphI I) l), cockpit := a # agra (graphI I) cockpit))
                          (cgra (graphI I)) (lgra (graphI I)))
                         (delta I) \<Longrightarrow>
                    a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) cockpit) \<Longrightarrow>
                    l' = cockpit \<Longrightarrow> h \<in> set (agra (graphI I) cockpit) \<Longrightarrow> h \<in> airplane_actors"
                by (erule bspec)
            next fix z z' h G I a l l' I'
              assume a0: "\<forall>h::char list\<in>set (agra (graphI I) cockpit). h \<in> airplane_actors"
and a1: "(Airplane_not_in_danger_init, I) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"       
and a2: "z = I"
and a3: "z' =
        Infrastructure
         (Lgraph (gra (graphI I))
           ((agra (graphI I))
            (l := del a (agra (graphI I) l), cockpit := a # agra (graphI I) cockpit))
           (cgra (graphI I)) (lgra (graphI I)))
         (delta I)"
and a4: "G = graphI I"
and a5: "a @\<^bsub>graphI I\<^esub> l"
and a6: "l \<in> nodes (graphI I)"
and a7: "cockpit \<in> nodes (graphI I)"
and a8: "a \<in> actors_graph (graphI I)"
and a9: "enables I cockpit (Actor a) move"
and a10: "I' =
         Infrastructure
           (Lgraph (gra (graphI I))
              ((agra (graphI I))
              (l := del a (agra (graphI I) l), cockpit := a # agra (graphI I) cockpit))
              (cgra (graphI I)) (lgra (graphI I)))
           (delta I)"
and a11: "a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) cockpit)"
and a12: "l' = cockpit" 
and a13: "h = a"
              show  "h \<in> airplane_actors"
              proof -
                have a: "delta(I) = delta(Airplane_not_in_danger_init)"
                  by (rule sym, rule init_state_policy, rule a1)
                show ?thesis 
                  by (insert a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a,
                      simp add: enables_def, erule bexE, simp add: Airplane_not_in_danger_init_def,
                      unfold local_policies_four_eyes_def, simp, erule disjE, simp+,
                      (* same trick as above show what Eve is not in the graph *)  
                      erule exE, (erule conjE)+,  
                      fold local_policies_four_eyes_def Airplane_not_in_danger_init_def,
                      drule all_airplane_actors, erule subst)
                    qed
                      qed
                        qed
                          qed
                        qed

lemma airplane_actors_inv: 
  assumes "(Airplane_not_in_danger_init,z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*" 
    shows "\<forall>h::char list\<in>set (agra (graphI z) cockpit). h \<in> airplane_actors"     
proof -
  have ind: "(Airplane_not_in_danger_init, z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<longrightarrow>
    (\<forall>h::char list\<in>set (agra (graphI z) cockpit). h \<in> airplane_actors)"
  proof (insert assms, erule rtrancl_induct)
    show "(Airplane_not_in_danger_init, Airplane_not_in_danger_init) \<in> {(x,y). x \<rightarrow>\<^sub>n y}\<^sup>* \<longrightarrow>
    (\<forall>h::char list\<in>set (agra (graphI Airplane_not_in_danger_init) cockpit). h \<in> airplane_actors)"
     by (rule impI, rule ballI,
         simp add: Airplane_not_in_danger_init_def ex_graph_def airplane_actors_def ex_locs_def, 
         blast)
    next show "\<And>(y::infrastructure) z::infrastructure.
       (Airplane_not_in_danger_init, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       (y, z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
       (Airplane_not_in_danger_init, y) \<in> {(x,y). x \<rightarrow>\<^sub>n y}\<^sup>* \<longrightarrow>
       (\<forall>h::char list\<in>set (agra (graphI y) cockpit). h \<in> airplane_actors) \<Longrightarrow>
       (Airplane_not_in_danger_init, z) \<in> {(x,y). x \<rightarrow>\<^sub>n y}\<^sup>* \<longrightarrow>
       (\<forall>h::char list\<in>set (agra (graphI z) cockpit). h \<in> airplane_actors)"
    by (rule impI, rule ballI, rule_tac z = y in airplane_actors_inv0, 
        rule conjI, erule impE, assumption+, simp)
  qed
  show ?thesis 
  by (insert ind, insert assms, simp)
qed
    
lemma Eve_not_in_cockpit: "(Airplane_not_in_danger_init, I)
       \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       x \<in> set (agra (graphI I) cockpit) \<Longrightarrow> x \<noteq> ''Eve''"
 by (drule airplane_actors_inv, simp add: airplane_actors_def,
     drule_tac x = x in bspec, assumption, force)
    
text \<open>The 2 person invariant implies that there is always some @{text \<open>x\<close>} in cockpit where
      @{text \<open>x\<close>} not equal @{text \<open>Eve\<close>}.\<close>
lemma tp_imp_control:
  assumes "(Airplane_not_in_danger_init,I) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
  shows "(? x :: identity.  x @\<^bsub>graphI I\<^esub> cockpit \<and> Actor x \<noteq> Actor ''Eve'')"
proof -
  have a0: "(2::nat) \<le> card (set (agra (graphI I) cockpit))" 
    by (insert assms, erule two_person_set_inv)
  have a1: "is_singleton({''Charly''})"
    by (rule is_singletonI)
  have a6: "\<not>(\<forall> x \<in> set(agra (graphI I) cockpit). (Actor x = Actor ''Eve''))"
    proof (rule notI)
      assume a7: " \<forall>x::char list\<in>set (agra (graphI I) cockpit). Actor x = Actor ''Eve''"
      have a5: "\<forall>x::char list\<in>set (agra (graphI I) cockpit). x = ''Charly''"
        by (insert assms a0 a7, rule ballI, drule_tac x = x in bspec, assumption, 
            subgoal_tac "x \<noteq> ''Eve''", insert Insider_Eve, unfold Insider_def, (drule mp), 
               rule Eve_precipitating_event, simp add: UasI_def, erule Eve_not_in_cockpit)
      have a4: "set (agra (graphI I) cockpit) = {''Charly''}"
        by (rule equalityI, rule subsetI, insert a5, simp,
            rule subsetI, simp, rule Set_all_unique, insert a0, force, rule a5)
      have a2: "(card((set (agra (graphI I) cockpit)) :: char list set)) = (1 :: nat)"
         by (insert a1, unfold is_singleton_altdef, erule ssubst, insert a4, erule ssubst,
             fold is_singleton_altdef, rule a1)
      have a3: "(2 :: nat) \<le> (1 ::nat)" 
         by (insert a0, insert a2, erule subst, assumption) 
      show False
        by (insert a5 a4 a3 a2, arith)
    qed
  show ?thesis  by (insert assms a0 a6, simp add: atI_def, blast)
qed

lemma Fend_2: "(Airplane_not_in_danger_init,I) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
         \<not> enables I cockpit (Actor ''Eve'') put"
  by (insert cockpit_foe_control, simp add: foe_control_def, drule_tac x = I in bspec,
         simp add: Air_tp_Kripke_def Air_tp_states_def state_transition_in_refl_def, 
         erule mp, erule tp_imp_control)
(*  by (insert cockpit_foe_control, simp add: foe_control_def, drule_tac x = I in spec,
      erule mp, erule tp_imp_control) *)

theorem Four_eyes_no_danger: "Air_tp_Kripke \<turnstile> AG ({x. global_policy x ''Eve''})"
proof (simp add: Air_tp_Kripke_def check_def, rule conjI)
  show "Airplane_not_in_danger_init \<in> Air_tp_states"
    by (simp add: Airplane_not_in_danger_init_def Air_tp_states_def
                    state_transition_in_refl_def)
next show "Airplane_not_in_danger_init \<in> AG {x::infrastructure. global_policy x ''Eve''}"
  proof (unfold AG_def, simp add: gfp_def,
   rule_tac x = "{(x :: infrastructure) \<in> states Air_tp_Kripke. ~(''Eve'' @\<^bsub>graphI x\<^esub> cockpit)}" in exI,
   rule conjI)
    show "{x::infrastructure \<in> states Air_tp_Kripke. \<not> ''Eve'' @\<^bsub>graphI x\<^esub> cockpit}
    \<subseteq> {x::infrastructure. global_policy x ''Eve''}"
     by (unfold global_policy_def, simp add: airplane_actors_def, rule subsetI,
         drule CollectD, rule CollectI, erule conjE,
         simp add: Air_tp_Kripke_def Air_tp_states_def state_transition_in_refl_def,
         erule Fend_2)
 next show "{x::infrastructure \<in> states Air_tp_Kripke. \<not> ''Eve'' @\<^bsub>graphI x\<^esub> cockpit}
    \<subseteq> AX {x::infrastructure \<in> states Air_tp_Kripke. \<not> ''Eve'' @\<^bsub>graphI x\<^esub> cockpit} \<and>
    Airplane_not_in_danger_init
    \<in> {x::infrastructure \<in> states Air_tp_Kripke. \<not> ''Eve'' @\<^bsub>graphI x\<^esub> cockpit}"
   proof
     show "Airplane_not_in_danger_init
          \<in> {x::infrastructure \<in> states Air_tp_Kripke. \<not> ''Eve'' @\<^bsub>graphI x\<^esub> cockpit}"
      by (simp add: Airplane_not_in_danger_init_def Air_tp_Kripke_def Air_tp_states_def
                    state_transition_refl_def ex_graph_def atI_def Air_tp_Kripke_def
                    state_transition_in_refl_def)
  next show "{x::infrastructure \<in> states Air_tp_Kripke. \<not> ''Eve'' @\<^bsub>graphI x\<^esub> cockpit}
    \<subseteq> AX {x::infrastructure \<in> states Air_tp_Kripke. \<not> ''Eve'' @\<^bsub>graphI x\<^esub> cockpit}"
    proof (rule subsetI, simp add: AX_def, rule subsetI, rule CollectI, rule conjI)
      show "\<And>(x::infrastructure) xa::infrastructure.
       x \<in> states Air_tp_Kripke \<and> \<not> ''Eve'' @\<^bsub>graphI x\<^esub> cockpit \<Longrightarrow>
       xa \<in> Collect (state_transition x) \<Longrightarrow> xa \<in> states Air_tp_Kripke"
        by (simp add:  Air_tp_Kripke_def Air_tp_states_def state_transition_in_refl_def,
            simp add: atI_def, erule conjE,
            unfold state_transition_infra_def state_transition_in_refl_def,
            erule rtrancl_into_rtrancl, rule CollectI, simp)
    next fix x xa
        assume a0: "x \<in> states Air_tp_Kripke \<and> \<not> ''Eve'' @\<^bsub>graphI x\<^esub> cockpit"
         and a1: "xa \<in> Collect (state_transition x)"
        show "\<not> ''Eve'' @\<^bsub>graphI xa\<^esub> cockpit"
      proof -
        have b: "(Airplane_not_in_danger_init, xa)
       \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
        proof (insert a0 a1, rule rtrancl_trans)
          show "x \<in> states Air_tp_Kripke \<and> \<not> ''Eve'' @\<^bsub>graphI x\<^esub> cockpit \<Longrightarrow>
                xa \<in> Collect (state_transition x) \<Longrightarrow>
                (x, xa) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
            by (unfold state_transition_infra_def, force)
        next show "x \<in> states Air_tp_Kripke \<and> \<not> ''Eve'' @\<^bsub>graphI x\<^esub> cockpit \<Longrightarrow>
                  xa \<in> Collect (state_transition x) \<Longrightarrow>
                  (Airplane_not_in_danger_init, x) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
            by (erule conjE, simp add: Air_tp_Kripke_def Air_tp_states_def state_transition_in_refl_def)+
        qed
        show ?thesis 
         by (insert a0 a1 b, rule_tac P = "''Eve'' @\<^bsub>graphI xa\<^esub> cockpit" in notI, 
            simp add: atI_def, drule Eve_not_in_cockpit, assumption, simp)
     qed       
   qed
 qed
qed
qed

(***** Generalisation (not possible in MC): 
       for any policy that implies the 2-person-rule the airplane is safe ****)
(* Generalisation of two_person_set_inv: if an initial state I fulfills
the 2-person-rule, then   state transition preserves the 2-person-inv. This is now for the
Gen_policy below. *)
(* The following can only be shown if there is a policy delta I0 that entails that
   there are *)
lemma two_person_inv_gen_one: 
      "z \<rightarrow>\<^sub>n z'
     \<Longrightarrow> (2::nat) \<le> length (agra (graphI z) cockpit)
     \<Longrightarrow> nodes(graphI z) = nodes(graphI I0)
     \<Longrightarrow> delta(I0) = delta z
     \<Longrightarrow> (I0, z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*
    \<Longrightarrow> (2::nat) \<le> length (agra (graphI z') cockpit)" 
proof (erule state_transition_in.cases, simp, subgoal_tac "l' = cabin \<or> l' = door \<or> l' = cockpit", erule disjE, simp)
  show \<open>\<And>G I a l l' I'.
       2 \<le> length (agra (graphI I) cockpit) \<Longrightarrow>
       nodes (graphI I) = nodes (graphI I0) \<Longrightarrow>
       delta I0 = delta I \<Longrightarrow>
       (I0, I) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = Infrastructure (move_graph_a a l cabin (graphI I)) (delta I) \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>graphI I\<^esub> l \<Longrightarrow>
       l \<in> nodes (graphI I0) \<Longrightarrow>
       cabin \<in> nodes (graphI I0) \<Longrightarrow>
       a \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I cabin (Actor a) move \<Longrightarrow>
       I' = Infrastructure (move_graph_a a l cabin (graphI I)) (delta I) \<Longrightarrow>
       l' = cabin \<Longrightarrow> 2 \<le> length (agra (move_graph_a a l cabin (graphI I)) cockpit)\<close>
       apply (subgoal_tac "delta I = local_policies_four_eyes")
       apply (simp add: enables_def local_policies_four_eyes_def)
proof -
  fix G :: igraph and I :: infrastructure and a :: "char list" and l :: location and l' :: location and I' :: infrastructure
  assume a1: "\<exists>x\<in>if cabin = cockpit then {(\<lambda>x. (\<exists>n. n @\<^bsub>graphI I\<^esub> cockpit \<and> Actor n = x) \<and> 2 \<le> length (agra (graphI I) cabin) \<and> (\<forall>h\<in>set (agra (graphI I) cabin). h \<in> airplane_actors), {put}), (\<lambda>x. \<exists>n. n @\<^bsub>graphI I\<^esub> cabin \<and> Actor n = x \<and> has (graphI I) (x, ''PIN'') \<and> isin (graphI I) door ''norm'', {move})} else if cabin = door then {(\<lambda>x. (\<exists>n. n @\<^bsub>graphI I\<^esub> cockpit \<and> Actor n = x) \<and> 3 \<le> length (agra (graphI I) cockpit), {move})} else if cabin = cabin then {(\<lambda>x. (\<exists>n. n @\<^bsub>graphI I\<^esub> door \<and> Actor n = x) \<and> 3 \<le> length (agra (graphI I) cockpit), {move})} else {}. case x of (p, e) \<Rightarrow> move \<in> e \<and> p (Actor a)"
  assume a2: "2 \<le> length (agra (graphI I) cockpit)"
  obtain pp :: "(actor \<Rightarrow> bool) \<times> action set" where
    f3: "pp \<in> (if cabin = cockpit then {(\<lambda>a. (\<exists>cs. cs @\<^bsub>graphI I\<^esub> cockpit \<and> Actor cs = a) \<and> 2 \<le> length (agra (graphI I) cabin) \<and> (\<forall>cs. cs \<in> set (agra (graphI I) cabin) \<longrightarrow> cs \<in> airplane_actors), {put}), (\<lambda>a. \<exists>cs. cs @\<^bsub>graphI I\<^esub> cabin \<and> Actor cs = a \<and> has (graphI I) (a, ''PIN'') \<and> isin (graphI I) door ''norm'', {move})} else if cabin = door then {(\<lambda>a. (\<exists>cs. cs @\<^bsub>graphI I\<^esub> cockpit \<and> Actor cs = a) \<and> 3 \<le> length (agra (graphI I) cockpit), {move})} else {(\<lambda>a. (\<exists>cs. cs @\<^bsub>graphI I\<^esub> door \<and> Actor cs = a) \<and> 3 \<le> length (agra (graphI I) cockpit), {move})}) \<and> (case pp of (p, A) \<Rightarrow> move \<in> A \<and> p (Actor a))"
    using a1 by meson
  have f4: "\<forall>n css cs. \<not> Suc n \<le> length css \<or> n \<le> length (del (cs::char list) css)"
    by (meson del_sort)
  have f5: "cabin \<noteq> cockpit"
    by (simp add: cabin_def cockpit_def)
  have f6: "pp = (\<lambda>a. (\<exists>cs. cs @\<^bsub>graphI I\<^esub> door \<and> Actor cs = a) \<and> 3 \<le> length (agra (graphI I) cockpit), {move}) \<longrightarrow> move \<in> {move} \<and> (\<exists>cs. cs @\<^bsub>graphI I\<^esub> door \<and> Actor cs = Actor a) \<and> 3 \<le> length (agra (graphI I) cockpit)"
    using f3 by blast
  { assume "pp \<notin> {(\<lambda>a. (\<exists>cs. cs @\<^bsub>graphI I\<^esub> cockpit \<and> Actor cs = a) \<and> 3 \<le> length (agra (graphI I) cockpit), {move})}"
    then have "move_graph_a a l cabin (graphI I) = Lgraph (gra (graphI I)) ((agra (graphI I)) (l := del a (agra (graphI I) l), cabin := a # agra (graphI I) cabin)) (cgra (graphI I)) (lgra (graphI I)) \<longrightarrow> 3 \<le> length (agra (graphI I) cockpit) \<and> move_graph_a a l cabin (graphI I) = Lgraph (gra (graphI I)) ((agra (graphI I)) (l := del a (agra (graphI I) l), cabin := a # agra (graphI I) cabin)) (cgra (graphI I)) (lgra (graphI I))"
      using f6 f5 f3 by (meson bex_empty insertE) }
  then have "move_graph_a a l cabin (graphI I) = Lgraph (gra (graphI I)) ((agra (graphI I)) (l := del a (agra (graphI I) l), cabin := a # agra (graphI I) cabin)) (cgra (graphI I)) (lgra (graphI I)) \<longrightarrow> 3 \<le> length (agra (graphI I) cockpit) \<and> move_graph_a a l cabin (graphI I) = Lgraph (gra (graphI I)) ((agra (graphI I)) (l := del a (agra (graphI I) l), cabin := a # agra (graphI I) cabin)) (cgra (graphI I)) (lgra (graphI I))"
    using f3 by blast
  then show "2 \<le> length (agra (move_graph_a a l cabin (graphI I)) cockpit)"
    using f4 a2 move_graph_a_def by auto
next show \<open>\<And>G I a l l' I'.
       2 \<le> length (agra (graphI I) cockpit) \<Longrightarrow>
       nodes (graphI I) = nodes (graphI I0) \<Longrightarrow>
       delta I0 = delta I \<Longrightarrow>
       (I0, I) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = Infrastructure (move_graph_a a l cabin (graphI I)) (delta I) \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>graphI I\<^esub> l \<Longrightarrow>
       l \<in> nodes (graphI I0) \<Longrightarrow>
       cabin \<in> nodes (graphI I0) \<Longrightarrow>
       a \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I cabin (Actor a) move \<Longrightarrow>
       I' = Infrastructure (move_graph_a a l cabin (graphI I)) (delta I) \<Longrightarrow>
       l' = cabin \<Longrightarrow> delta I = local_policies_four_eyes\<close>
  sorry
(*
apply (erule state_transition_in.cases)
     apply simp
     apply (subgoal_tac "l' = cabin \<or> l' = door \<or> l' = cockpit")
      apply (erule disjE)
       apply simp
       apply (subgoal_tac "delta Ia = local_policies_four_eyes")
        apply (simp add: enables_def local_policies_four_eyes_def)
        apply (erule bexE)
  apply (unfold local_policies_four_eyes_def)
apply (case_tac x)
        apply simp
  apply (subgoal_tac "(aa, b)
       \<in> {(\<lambda>x. (\<exists>n. n @\<^bsub>graphI Ia\<^esub> door \<and> Actor n = x) \<and> 3 \<le> length (agra (graphI Ia) cockpit), {move})}")
         apply (subgoal_tac "3 \<le> length (agra (graphI Ia) cockpit)")
          prefer 2
  apply simp
          apply (simp add: move_graph_a_def)
  apply (metis (no_types, lifting) cabin_def cockpit_def del_sort location.inject numeral_2_eq_2 numeral_3_eq_3)
  apply (simp add: cabin_def cockpit_def door_def)
  apply simp
(* *)
  apply (erule disjE)
       apply simp
       apply (subgoal_tac "delta I = local_policies_four_eyes")
        apply (simp add: enables_def local_policies_four_eyes_def)
        apply (erule bexE)
  apply (unfold Airplane_not_in_danger_init_def local_policies_four_eyes_def)
        apply simp
         apply (case_tac x)
        apply simp
  apply (subgoal_tac "(aa,b) \<in>
{(\<lambda>x. (\<exists>n. n @\<^bsub>graphI I\<^esub> cockpit \<and> Actor n = x) \<and>
                           3 \<le> length (agra (graphI I) cockpit),
                       {move})}")
         apply (subgoal_tac "3 \<le> length (agra (graphI I) cockpit)")
          prefer 2
  apply simp
          apply (simp add: move_graph_a_def)
  apply (metis (no_types, lifting) One_nat_def cockpit_def del_sort door_def location.inject numeral_2_eq_2 numeral_3_eq_3)
  apply (simp add: cabin_def cockpit_def door_def)
       apply simp
(* l' = cockpit *)
       apply simp
       apply (subgoal_tac "delta I = local_policies_four_eyes")
        apply (simp add: enables_def local_policies_four_eyes_def)
        apply (erule exE)
  apply (unfold Airplane_not_in_danger_init_def local_policies_four_eyes_def)
        apply simp
       apply (simp add: move_graph_a_def)
      apply simp
  using not_enableI apply force
(* get *)
  apply simp
(* *)
   apply simp
(* *)
  by simp
*)
  oops

lemma two_person_gen_inv1:
  assumes "(I0,z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*" 
      and "(2::nat) \<le> length (agra (graphI I0) cockpit)"
      and "\<forall> I I'. I \<rightarrow>\<^sub>n I' \<longrightarrow>  2 \<le> length (agra (graphI I) cockpit) \<longrightarrow>  2 \<le> length (agra (graphI I') cockpit)"
  shows "(2::nat) \<le> length (agra (graphI z) cockpit)" 
proof (insert assms, erule rtrancl_induct) 
  show "2 \<le> length (agra (graphI I0) cockpit) \<Longrightarrow> (2::nat) \<le> length (agra (graphI I0) cockpit)" .
next show \<open>\<And>y z. 2 \<le> length (agra (graphI I0) cockpit) \<Longrightarrow>
           (I0, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow> 2 \<le> length (agra (graphI y) cockpit) \<Longrightarrow> 2 \<le> length (agra (graphI z) cockpit) \<close>
    using assms(3) by auto
qed
(*
lemma two_person_set_inv_gen: 
  assumes "(I, z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*" 
     and "(2::nat) \<le> card (set (agra (graphI I) cockpit))"
     and "\<forall>a. (\<forall>l l'. ((a @\<^bsub>graphI I\<^esub> l) \<and> (a @\<^bsub>graphI I\<^esub> l')) \<longrightarrow> l = l') \<and> (\<forall>l. nodup a (agra (graphI I) l))"
    shows "(2::nat) \<le> card (set (agra (graphI z) cockpit))"
proof -
  have a: "card (set (agra (graphI z) cockpit)) = length(agra (graphI z) cockpit)"
    by (meson actors_unique_loc_step assms(1) assms(3) no_dup_set_list_num_eq)
  show ?thesis
    using a assms(1) assms(2) card_length order.trans two_person_gen_inv1 by fastforce 
qed
*)

theorem Gen_policy: 
  assumes "(I0, z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*" 
     and "(2::nat) \<le> card (set (agra (graphI I0) cockpit))"
      and "\<forall> I I'. I \<rightarrow>\<^sub>n I' \<longrightarrow>  2 \<le> length (agra (graphI I) cockpit) \<longrightarrow>  2 \<le> length (agra (graphI I') cockpit)"
   shows "Kripke  { I. I0 \<rightarrow>\<^sub>n* I } {I0} \<turnstile> AG {x. global_policy x ''Eve''}"

  sorry
(*  by (metis Airplane_not_in_danger_init_def Airplane_scenario_def airplane.cockpit_foe_control airplane_axioms cockpit_def ex_inv3 global_policy_def graphI.simps rtrancl.intros(1) tp_imp_control)
*)
end

subsection \<open>Locale interpretation\<close>

text \<open>In the following we construct an instance of the locale airplane and proof
   that it is an interpretation. This serves the validation.\<close> 
definition airplane_actors_def': "airplane_actors \<equiv> {''Bob'', ''Charly'', ''Alice''}"
definition airplane_locations_def': 
"airplane_locations \<equiv> {Location 0, Location 1, Location 2}"
definition cockpit_def': "cockpit \<equiv> Location 2"
definition door_def': "door \<equiv> Location 1" 
definition cabin_def': "cabin \<equiv> Location 0" 
definition global_policy_def': "global_policy I a \<equiv> a \<notin> airplane_actors 
                 \<longrightarrow> \<not>(enables I cockpit (Actor a) put)"
definition ex_creds_def': "ex_creds \<equiv> 
        (\<lambda> x.(if x = Actor ''Bob'' 
              then ([''PIN''], [''pilot''])        
              else (if x = Actor ''Charly'' 
                    then ([''PIN''],[''copilot''])
                    else (if x = Actor ''Alice''  
                          then ([''PIN''],[''flightattendant''])
                                else ([],[])))))"

definition ex_locs_def': "ex_locs \<equiv>  (\<lambda> x. if x = door then [''norm''] else 
                                       (if x = cockpit then [''air''] else []))"
  
definition ex_locs'_def': "ex_locs' \<equiv>  (\<lambda> x. if x = door then [''locked''] else
                                         (if x = cockpit then [''air''] else []))"
  
definition ex_graph_def': "ex_graph \<equiv> Lgraph
      {(cockpit, door),(door,cabin)}
      (\<lambda> x. if x = cockpit then [''Bob'', ''Charly''] 
            else (if x = door then [] 
                  else (if x = cabin then [''Alice''] else [])))
      ex_creds ex_locs"

definition aid_graph_def': "aid_graph \<equiv>  Lgraph
      {(cockpit, door),(door,cabin)}
      (\<lambda> x. if x = cockpit then [''Charly''] 
            else (if x = door then [] 
                  else (if x = cabin then [''Bob'', ''Alice''] else [])))
      ex_creds ex_locs'"
  
definition aid_graph0_def': "aid_graph0 \<equiv>  Lgraph
      {(cockpit, door),(door,cabin)}
      (\<lambda> x. if x = cockpit then [''Charly''] 
            else (if x = door then [''Bob''] 
                  else (if x = cabin then [''Alice''] else [])))
        ex_creds ex_locs"

definition agid_graph_def': "agid_graph \<equiv>  Lgraph
      {(cockpit, door),(door,cabin)}
      (\<lambda> x. if x = cockpit then [''Charly''] 
            else (if x = door then [] 
                  else (if x = cabin then [''Bob'', ''Alice''] else [])))
      ex_creds ex_locs"
  
definition local_policies_def': "local_policies G \<equiv>  
   (\<lambda> y. if y = cockpit then
             {(\<lambda> x. (? n. (n @\<^bsub>G\<^esub> cockpit) \<and> Actor n = x), {put}),
              (\<lambda> x. (? n. (n @\<^bsub>G\<^esub> cabin) \<and> Actor n = x \<and> has G (x, ''PIN'')
                    \<and> isin G door ''norm''),{move})
             }
         else (if y = door then {(\<lambda> x. True, {move}),
                       (\<lambda> x. (? n. (n @\<^bsub>G\<^esub> cockpit) \<and> Actor n = x), {put})}
               else (if y = cabin then {(\<lambda> x. True, {move})} 
                     else {})))"
definition local_policies_four_eyes_def': "local_policies_four_eyes G \<equiv>  
   (\<lambda> y. if y = cockpit then
             {(\<lambda> x.  (? n. (n @\<^bsub>G\<^esub> cockpit) \<and> Actor n = x) \<and>
                     2 \<le> length(agra G y) \<and> (\<forall> h \<in> set(agra G y). h \<in> airplane_actors), {put}),
              (\<lambda> x. (? n. (n @\<^bsub>G\<^esub> cabin) \<and> Actor n = x \<and> has G (x, ''PIN'') \<and> 
                           isin G door ''norm'' ),{move})
             }
         else (if y = door then 
              {(\<lambda> x.  ((? n. (n @\<^bsub>G\<^esub> cockpit) \<and> Actor n = x) \<and> 3 \<le> length(agra G cockpit)), {move})}
               else (if y = cabin then 
                     {(\<lambda> x. ((? n. (n @\<^bsub>G\<^esub> door) \<and> Actor n = x)\<and> 3 \<le> length(agra G cockpit)), {move})} 
                           else {})))"

definition Airplane_scenario_def':
"Airplane_scenario \<equiv> Infrastructure ex_graph local_policies"

definition Airplane_in_danger_def':
"Airplane_in_danger \<equiv> Infrastructure aid_graph local_policies"

text \<open>This is the intermediate step where pilot left the cockpit but the door is still in
   norm position.\<close>
definition Airplane_getting_in_danger0_def':
"Airplane_getting_in_danger0 \<equiv> Infrastructure aid_graph0 local_policies"

definition Airplane_getting_in_danger_def':
"Airplane_getting_in_danger \<equiv> Infrastructure agid_graph local_policies"

definition Air_states_def': "Air_states \<equiv> { I. Airplane_scenario \<rightarrow>\<^sub>n* I }"

definition Air_Kripke_def': "Air_Kripke \<equiv> Kripke Air_states {Airplane_scenario}"

definition Airplane_not_in_danger_def': 
"Airplane_not_in_danger \<equiv> Infrastructure aid_graph local_policies_four_eyes"

definition Airplane_not_in_danger_init_def':
"Airplane_not_in_danger_init \<equiv> Infrastructure ex_graph local_policies_four_eyes"

definition Air_tp_states_def': "Air_tp_states \<equiv> { I. Airplane_not_in_danger_init \<rightarrow>\<^sub>n* I }"

definition Air_tp_Kripke_def':
"Air_tp_Kripke \<equiv> Kripke Air_tp_states {Airplane_not_in_danger_init}"

definition Safety_def': "Safety I a \<equiv> a \<in> airplane_actors  
                       \<longrightarrow> (enables I cockpit (Actor a) move)"

definition Security_def': "Security I a \<equiv>  (isin (graphI I) door ''locked'') 
                       \<longrightarrow> \<not>(enables I cockpit (Actor a) move)"

definition foe_control_def': "foe_control l c K \<equiv>  
   (\<forall> I:: infrastructure \<in> states K. (? x :: identity. 
        x @\<^bsub>graphI I\<^esub> l \<and> Actor x \<noteq> Actor ''Eve'')
             \<longrightarrow> \<not>(enables I l (Actor ''Eve'') c))"

definition astate_def': "astate x \<equiv>  
          (case x of 
           ''Eve'' \<Rightarrow> Actor_state depressed {revenge, peer_recognition}
          | _ \<Rightarrow> Actor_state happy {})"

print_interps airplane

text \<open>The additional assumption identified in the case study needs to be given as an axiom\<close>
axiomatization where
cockpit_foe_control': "foe_control cockpit put Air_tp_Kripke"

text \<open>The following addresses the issue of redefining an abstract type.
   We experimented with suggestion given in \cite{mw:09}.
  Following this, we need axiomatization to add the missing semantics to the
  abstractly declared type actor and thereby be able to redefine @{text \<open>consts Actor\<close>}.
  Since the function Actor has also been defined as a @{text \<open>consts :: identity \<Rightarrow> actor\<close>}
  as an abstract function without a definition, we now also now add its semantics
  mimicking some of the concepts of the conservative type definition of HOL.
  The alternative method of using a locale to replace the abstract @{text \<open>type_decl actor\<close>} 
  in the theory @{text \<open>AirInsider\<close>} is a more elegant method for representing an abstract 
  type @{text \<open>actor\<close>} but it is not working properly for our framework since it necessitates 
  introducing a type parameter @{text \<open>'actor\<close>} into infrastructures which then makes it 
  impossible to instantiate them to the @{text \<open>typeclass\<close>} state in order to use CTL and 
  Kripke and the generic state transition. 
  Therefore, we go the former way of a post-hoc axiomatic redefinition of the 
  abstract type actor by using axiomatization of the existing locale @{text \<open>type_definition\<close>}.
  This is done in the following. It allows to abstractedly assume as an axiom
  that there is a type definition for the abstract type actor. Adding a suitable
  definition of a representation for this type then additionally enables to introduce
  a definition for the function Actor (again using axiomatization to enforce the new
  definition).\<close>
   
definition Actor_Abs :: "identity \<Rightarrow> identity option"
  where 
"Actor_Abs x \<equiv> (if x \<in> {''Eve'', ''Charly''} then None else Some x)"

lemma UasI_ActorAbs: "Actor_Abs ''Eve'' = Actor_Abs ''Charly'' \<and>
    (\<forall>(x::char list) y::char list. x \<noteq> ''Eve'' \<and> y \<noteq> ''Eve'' \<and> Actor_Abs x = Actor_Abs y \<longrightarrow> x = y)"
  by (simp add: Actor_Abs_def)

lemma Actor_Abs_ran: "Actor_Abs x \<in> {y :: identity option. y \<in> Some ` {x :: identity. x \<notin> {''Eve'', ''Charly''}}| y = None}"
  by (simp add: Actor_Abs_def)

text \<open>With the following axiomatization, we can simulate the abstract type actor
   and postulate some unspecified @{text \<open>Abs\<close>} and @{text \<open>Rep\<close>} functions between it and the
   simulated identity option subtype.\<close>
axiomatization where Actor_type_def: 
"type_definition (Rep :: actor \<Rightarrow> identity option)(Abs :: identity option \<Rightarrow> actor) 
{y :: identity option. y \<in> Some ` {x :: identity. x \<notin> {''Eve'', ''Charly''}}| y = None}"

lemma Abs_inj_on: "\<And> Abs Rep:: actor \<Rightarrow> char list option. x \<in> {y :: identity option. y \<in> Some ` {x :: identity. x \<notin> {''Eve'', ''Charly''}}| y = None}  
               \<Longrightarrow> y \<in> {y :: identity option. y \<in> Some ` {x :: identity. x \<notin> {''Eve'', ''Charly''}}| y = None}
               \<Longrightarrow> (Abs :: char list option \<Rightarrow> actor) x = Abs y \<Longrightarrow> x = y"
by (insert Actor_type_def, drule_tac x = Rep in meta_spec, drule_tac x = Abs in meta_spec,
   frule_tac x = "Abs x" and y = "Abs y" in type_definition.Rep_inject,
   subgoal_tac "(Rep (Abs x) = Rep (Abs y))", subgoal_tac "Rep (Abs x) = x",
   subgoal_tac "Rep (Abs y) = y", erule subst, erule subst, assumption,
   (erule type_definition.Abs_inverse, assumption)+, simp)

lemma Actor_td_Abs_inverse: 
"(y\<in> {y :: identity option. y \<in> Some ` {x :: identity. x \<notin> {''Eve'', ''Charly''}}| y = None}) \<Longrightarrow> 
(Rep :: actor \<Rightarrow> identity option)((Abs :: identity option \<Rightarrow> actor) y) = y"
by (insert Actor_type_def, drule_tac x = Rep in meta_spec, drule_tac x = Abs in meta_spec,
  erule type_definition.Abs_inverse, assumption)

text \<open>Now, we can redefine the function @{text \<open>Actor\<close>} using a second axiomatization\<close>
axiomatization where Actor_redef: "Actor = (Abs :: identity option \<Rightarrow> actor)o Actor_Abs"

text \<open>We need to show that 

@{term "Abs(Actor_Abs x) = Abs(Actor_Abs y) \<longrightarrow> Actor_Abs x = Actor_Abs y"},
i.e. @{text "injective Abs"}. 

Generally, @{text \<open>Abs\<close>} is not injective but @{text "injective_on"} the type predicate.
So, we need to show that for any x, @{text "Actor_Abs x"} is in the type predicate, then it 
would follow.
This is the type predicate:

@{term "{y :: identity option. y \<in> Some`{x :: identity. x \<notin> {''Eve'', ''Charly''}} | y = None}"}.\<close>
lemma UasI_Actor_redef: 
"\<And> Abs Rep:: actor \<Rightarrow> char list option. 
((Abs :: identity option \<Rightarrow> actor)o Actor_Abs) ''Eve'' = ((Abs :: identity option \<Rightarrow> actor)o Actor_Abs) ''Charly'' \<and>
    (\<forall>(x::char list) y::char list. x \<noteq> ''Eve'' \<and> y \<noteq> ''Eve'' \<and> 
  ((Abs :: identity option \<Rightarrow> actor)o Actor_Abs) x = ((Abs :: identity option \<Rightarrow> actor)o Actor_Abs) y 
   \<longrightarrow> x = y)"
by (insert UasI_ActorAbs, simp, clarify, drule_tac x = x in spec, drule_tac x = y in spec,
    subgoal_tac "Actor_Abs x = Actor_Abs y", simp, rule Abs_inj_on, rule Actor_Abs_ran, rule Actor_Abs_ran)

text \<open>Finally all of this allows us to show the last assumption contained in the
   Insider Locale assumption needed for the interpretation of airplane.\<close>
lemma UasI_Actor: "UasI ''Eve'' ''Charly''"
 by (unfold UasI_def, insert Actor_redef, drule meta_spec, erule ssubst, rule UasI_Actor_redef)

interpretation airplane airplane_actors airplane_locations cockpit door cabin global_policy 
               ex_creds ex_locs ex_locs' ex_graph aid_graph aid_graph0 agid_graph 
               local_policies local_policies_four_eyes Airplane_scenario Airplane_in_danger
               Airplane_getting_in_danger0 Airplane_getting_in_danger Air_states Air_Kripke
               Airplane_not_in_danger Airplane_not_in_danger_init Air_tp_states 
               Air_tp_Kripke Safety Security foe_control astate
apply (rule airplane.intro, simp add: tipping_point_def)
  apply (simp add: Insider_def UasI_def tipping_point_def atI_def)
                      apply ( insert UasI_Actor, simp add: UasI_def)
                      apply (insert cockpit_foe_control')
                      apply (rule ballI)
  apply (simp add: foe_control_def')
                      apply (drule_tac x = I in bspec)
apply (unfold Air_tp_Kripke_def'
                             Air_tp_states_def' Airplane_not_in_danger_init_def'
                             ex_graph_def' ex_creds_def' ex_locs_def' local_policies_four_eyes_def'
                            foe_control_def' cockpit_def' door_def' cabin_def' airplane_actors_def')
                      apply simp
  apply assumption
  apply (simp add: local_policies_four_eyes_def')
apply
    (simp add: airplane_actors_def' airplane_locations_def' cockpit_def' door_def' cabin_def' global_policy_def'
               ex_creds_def' ex_locs_def' ex_locs'_def' ex_graph_def' aid_graph_def' aid_graph0_def' 
               agid_graph_def' local_policies_def' local_policies_four_eyes_def' Airplane_scenario_def'
               Airplane_in_danger_def' Airplane_getting_in_danger0_def' Airplane_getting_in_danger_def'
               Air_states_def'  Air_Kripke_def' Airplane_not_in_danger_def' Airplane_not_in_danger_init_def'
               Air_tp_states_def' Air_tp_Kripke_def' Safety_def' Security_def' 
               foe_control_def' astate_def')+ 
                      apply (unfold cockpit_def', rule reflexive)
apply
    (simp add: airplane_actors_def' airplane_locations_def' cockpit_def' door_def' cabin_def' global_policy_def'
               ex_creds_def' ex_locs_def' ex_locs'_def' ex_graph_def' aid_graph_def' aid_graph0_def' 
               agid_graph_def' local_policies_def' local_policies_four_eyes_def' Airplane_scenario_def'
               Airplane_in_danger_def' Airplane_getting_in_danger0_def' Airplane_getting_in_danger_def'
               Air_states_def'  Air_Kripke_def' Airplane_not_in_danger_def' Airplane_not_in_danger_init_def'
               Air_tp_states_def' Air_tp_Kripke_def' Safety_def' Security_def' 
               foe_control_def' astate_def')+ 
                   apply (unfold cabin_def' door_def', rule reflexive)
                   apply (unfold aid_graph0_def' ex_creds_def' ex_locs_def'
                          cockpit_def'  door_def' cabin_def', rule reflexive)
                   apply (unfold agid_graph_def' ex_creds_def' ex_locs_def'
                          cockpit_def'  door_def' cabin_def', rule reflexive)
                   apply (unfold local_policies_def' ex_creds_def' ex_locs_def'
                          cockpit_def'  door_def' cabin_def', rule reflexive)
  apply (rule reflexive)
               apply (unfold Airplane_scenario_def' ex_graph_def' local_policies_def' 
                          ex_creds_def' ex_locs_def'
                          cockpit_def'  door_def' cabin_def', rule reflexive)
 apply (unfold Airplane_in_danger_def' ex_graph_def' local_policies_def' 
                          ex_creds_def' ex_locs_def'
                          cockpit_def'  door_def' cabin_def', rule reflexive)
 apply (unfold Airplane_getting_in_danger0_def' aid_graph0_def' ex_graph_def' local_policies_def' 
                          ex_creds_def' ex_locs_def'
                          cockpit_def'  door_def' cabin_def', rule reflexive)
 apply (unfold Airplane_getting_in_danger_def' agid_graph_def' ex_graph_def' local_policies_def' 
                          ex_creds_def' ex_locs_def'
                          cockpit_def'  door_def' cabin_def', rule reflexive)
 apply (unfold Air_states_def' Airplane_scenario_def' ex_graph_def' local_policies_def' 
                          ex_creds_def' ex_locs_def'
                          cockpit_def'  door_def' cabin_def', rule reflexive)
 apply (unfold Air_Kripke_def' Air_states_def' Airplane_scenario_def' ex_graph_def' local_policies_def' 
                          ex_creds_def' ex_locs_def'
                          cockpit_def'  door_def' cabin_def', rule reflexive)
 apply (unfold Airplane_not_in_danger_def' aid_graph_def' ex_graph_def' local_policies_four_eyes_def' 
                          ex_creds_def' ex_locs_def' airplane_actors_def'
                          cockpit_def'  door_def' cabin_def', rule reflexive)
        apply (rule reflexive)+
  apply (unfold Safety_def' airplane_actors_def' cockpit_def', rule reflexive)
    apply (unfold Security_def' airplane_actors_def' cockpit_def' door_def', rule reflexive)
       apply (rule reflexive)
by (unfold astate_def', rule reflexive)

(*
by (rule airplane.intro, simp add: tipping_point_def,
     simp add: Insider_def UasI_def tipping_point_def atI_def, 
     insert UasI_Actor, simp add: UasI_def,
      insert cockpit_foe_control', simp add: foe_control_def' cockpit_def',
     rule airplane_actors_def',
    (simp add: airplane_locations_def' cockpit_def' door_def' cabin_def' global_policy_def'
               ex_creds_def' ex_locs_def' ex_locs'_def' ex_graph_def' aid_graph_def' aid_graph0_def' 
               agid_graph_def' local_policies_def' local_policies_four_eyes_def' Airplane_scenario_def'
               Airplane_in_danger_def' Airplane_getting_in_danger0_def' Airplane_getting_in_danger_def'
               Air_states_def'  Air_Kripke_def' Airplane_not_in_danger_def' Airplane_not_in_danger_init_def'
               Air_tp_states_def' Air_tp_Kripke_def' Safety_def' Security_def' 
               foe_control_def' astate_def')+)
*)
end
    
    
