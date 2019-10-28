theory Airplane
imports AirInsider
begin

declare [[show_types]]
 
datatype doorstate = locked | norm | unlocked
datatype position = air | airport | ground


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
  
  
  
fixes local_policies :: "[igraph,  location] \<Rightarrow> policy set"
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
fixes local_policies_four_eyes :: "[igraph, location] \<Rightarrow> policy set"
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
                     {(\<lambda> x. ((? n. (n @\<^bsub>G\<^esub> door) \<and> Actor n = x)), {move})} 
                           else {})))"



fixes Airplane_scenario :: "infrastructure"
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

fixes foe_control :: "[location, action] \<Rightarrow> bool"
defines foe_control_def: "foe_control l c \<equiv>  
   (! I:: infrastructure. (? x :: identity. 
        x @\<^bsub>graphI I\<^esub> l \<and> Actor x \<noteq> Actor ''Eve'')
             \<longrightarrow> \<not>(enables I l (Actor ''Eve'') c))"
  
assumes Eve_precipitating_event: "tipping_point (astate ''Eve'')"
assumes Insider_Eve: "Insider ''Eve'' {''Charly''}"
assumes isin_inj: "\<forall> G. inj (isin G door)"
assumes cockpit_foe_control: "foe_control cockpit put"

begin

lemma ex_inv: "global_policy Airplane_scenario ''Bob''"
by (simp add: Airplane_scenario_def global_policy_def airplane_actors_def)

lemma ex_inv2: "global_policy Airplane_scenario ''Charly''"
by (simp add: Airplane_scenario_def global_policy_def airplane_actors_def)

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

(* show Safety for Airplane_scenario*)
lemma Safety: "Safety Airplane_scenario (''Alice'')"
proof -
  show "Safety Airplane_scenario ''Alice''"
    by (simp add: Airplane_scenario_def Safety_def enables_def ex_creds_def 
                local_policies_def ex_graph_def cockpit_def, rule impI,
        rule_tac x = "''Alice''" in exI, simp add: atI_def cabin_def ex_locs_def door_def,
        rule conjI, simp add: has_def credentials_def, simp add: isin_def credentials_def)
qed

(* show Security for Airplane_scenario *)
lemma inj_lem: "\<lbrakk> inj f; x \<noteq> y \<rbrakk> \<Longrightarrow> f x \<noteq> f y"
by (simp add: inj_eq)

lemma locl_lemma0: "isin G door ''norm'' \<noteq> isin G door ''locked''"
by (rule_tac f = "isin G door" in inj_lem, simp add: isin_inj, simp)

lemma locl_lemma: "isin G door ''norm'' = (\<not> isin G door ''locked'')"
by (insert locl_lemma0, blast)

lemma Security: "Security Airplane_scenario s"
by (simp add: Airplane_scenario_def Security_def enables_def local_policies_def ex_locs_def locl_lemma)

(* show that pilot can't get into cockpit if outside and locked = Airplane_in_danger *)
lemma Security_problem: "Security Airplane_scenario ''Bob''"
by (rule Security)

(* show that pilot can get out of cockpit *)
lemma pilot_can_leave_cockpit: "(enables Airplane_scenario cabin (Actor ''Bob'') move)"
  by (simp add: Airplane_scenario_def Security_def ex_creds_def ex_graph_def enables_def 
                local_policies_def ex_locs_def, simp add: cockpit_def cabin_def door_def)

(* show that in Airplane_in_danger copilot can still do put = put position to ground *)
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

(* declare [[show_types = true]] *)

(* The following two props should just be the opposite *) 
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
       ex_locs_def locl_lemma, rule impI)
  assume "has aid_graph (Actor ''Bob'', ''PIN'')"
  show "(\<forall>n::char list.
        Actor n = Actor ''Bob'' \<longrightarrow> n @\<^bsub>aid_graph\<^esub> cabin \<longrightarrow> isin aid_graph door ''locked'')"
by (simp add: aid_graph_def isin_def ex_locs'_def)
qed

(* show that with the four eyes rule in Airplane_not_in_danger Eve cannot 
   crash plane, i.e. cannot put position to ground *)
lemma ex_inv5: "a \<in> airplane_actors \<longrightarrow> global_policy Airplane_not_in_danger a"
by (simp add: Airplane_not_in_danger_def global_policy_def)

lemma ex_inv6: "global_policy Airplane_not_in_danger a"
proof (simp add: Airplane_not_in_danger_def global_policy_def, rule impI)
  assume "a \<notin> airplane_actors"
  show "\<not> enables (Infrastructure aid_graph local_policies_four_eyes) cockpit (Actor a) put"
by (simp add: aid_graph_def ex_locs'_def enables_def local_policies_four_eyes_def)
qed
  
(* 16. June 2017: start using state change from MC *)
(* 29. June 2017: start doing proofs *)
(* 5. July 2017: finished step proofs *)
(* August and September 2017: reworked semantics of tspace and lspace; work on
                 AG property example *) 
(* October 2017: realised that AG cannot be proved but leads to establishment
    of new necessary assumption *)
(* October 2018: upgraded to fully fledged Kripke structures with a generic state
    typed and allows instantiating this to airplane infrastructure as state.
   Change is visible in \<rightarrow>\<^sub>n instead of \<rightarrow>\<^sub>i as before *)  
  
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

    
(* Invariant: actors cannot be at two places at the same time*)  
lemma  actors_unique_loc_base: 
  assumes "I \<rightarrow>\<^sub>n I'"
      and "(\<forall> l l'. a @\<^bsub>graphI I\<^esub> l \<and> a @\<^bsub>graphI I\<^esub> l' \<longrightarrow> l = l')\<and>
           (\<forall> l. nodup a (agra (graphI I) l))"
    shows "(\<forall> l l'. a @\<^bsub>graphI I'\<^esub> l \<and> a @\<^bsub>graphI I'\<^esub> l'  \<longrightarrow> l = l') \<and>
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
       (\<forall>(l::location) l'::location. a @\<^bsub>graphI I'\<^esub> l \<and> a @\<^bsub>graphI I'\<^esub> l' \<longrightarrow> l = l') \<and>
       (\<forall>l::location. nodup a (agra (graphI I') l))" using assms
    by (simp add: atI_def)
next fix G Ia aa l I'a z
  assume a0: "I = Ia" and a1: "I' = I'a" and a2: "G = graphI Ia" and a3: "aa @\<^bsub>G\<^esub> l"
     and a4: "enables Ia l (Actor aa) put" 
     and a5: "I'a = Infrastructure (Lgraph (gra G) (agra G) (cgra G) ((lgra G)(l := [z]))) (delta Ia)"
  show "(\<forall>(l::location) l'::location. a @\<^bsub>graphI I'\<^esub> l \<and> a @\<^bsub>graphI I'\<^esub> l' \<longrightarrow> l = l') \<and>
       (\<forall>l::location. nodup a (agra (graphI I') l))"using assms
    by (simp add: a0 a1 a2 a3 a4 a5 atI_def)
next show "\<And>(G::igraph) (Ia::infrastructure) (l::location) (aa::char list) (I'a::infrastructure)
       z::char list.
       I = Ia \<Longrightarrow>
       I' = I'a \<Longrightarrow>
       G = graphI Ia \<Longrightarrow>
       enables Ia l (Actor aa) put \<Longrightarrow>
       I'a = Infrastructure (Lgraph (gra G) (agra G) (cgra G) ((lgra G)(l := [z]))) (delta Ia) \<Longrightarrow>
       (\<forall>(l::location) l'::location. a @\<^bsub>graphI I'\<^esub> l \<and> a @\<^bsub>graphI I'\<^esub> l' \<longrightarrow> l = l') \<and>
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
       (\<forall>(l::location) l'::location. a @\<^bsub>graphI I'\<^esub> l \<and> a @\<^bsub>graphI I'\<^esub> l' \<longrightarrow> l = l') \<and>
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
           a @\<^bsub>Lgraph (gra (graphI I)) (agra (graphI I)) (cgra (graphI I)) (lgra (graphI I))\<^esub> l \<and>
           a @\<^bsub>Lgraph (gra (graphI I)) (agra (graphI I)) (cgra (graphI I)) (lgra (graphI I))\<^esub> l' \<longrightarrow>
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
            a @\<^bsub>Lgraph (gra (graphI Ia))
                 ((agra (graphI Ia))
                  (l := del aa (agra (graphI Ia) l), l' := aa # agra (graphI Ia) l'))
                 (cgra (graphI Ia)) (lgra (graphI Ia))\<^esub> la \<and>
            a @\<^bsub>Lgraph (gra (graphI Ia))
                 ((agra (graphI Ia))
                  (l := del aa (agra (graphI Ia) l), l' := aa # agra (graphI Ia) l'))
                 (cgra (graphI Ia)) (lgra (graphI Ia))\<^esub> l'a \<longrightarrow>
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
            a @\<^bsub>Lgraph (gra (graphI Ia)) (agra (graphI Ia)) (cgra (graphI Ia))
                 (lgra (graphI Ia))\<^esub> l \<and>
            a @\<^bsub>Lgraph (gra (graphI Ia)) (agra (graphI Ia)) (cgra (graphI Ia))
                 (lgra (graphI Ia))\<^esub> l' \<longrightarrow>
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
      and "\<forall> a. (\<forall> l l'. a @\<^bsub>graphI I\<^esub> l \<and> a @\<^bsub>graphI I\<^esub> l' \<longrightarrow> l = l')\<and>
          (\<forall> l. nodup a (agra (graphI I) l))" 
    shows   "\<forall> a. (\<forall> l l'. a @\<^bsub>graphI I'\<^esub> l \<and> a @\<^bsub>graphI I'\<^esub> l'  \<longrightarrow> l = l') \<and>
          (\<forall> l. nodup a (agra (graphI I') l))"
proof -
  have ind: "(\<forall> a. (\<forall> l l'. a @\<^bsub>graphI I\<^esub> l \<and> a @\<^bsub>graphI I\<^esub> l' \<longrightarrow> l = l')\<and>
          (\<forall> l. nodup a (agra (graphI I) l))) \<longrightarrow>
       (\<forall> a. (\<forall> l l'. a @\<^bsub>graphI I'\<^esub> l \<and> a @\<^bsub>graphI I'\<^esub> l'  \<longrightarrow> l = l') \<and>
          (\<forall> l. nodup a (agra (graphI I') l)))"
  proof (insert assms(1), erule rtrancl.induct)
    show "\<And>a::infrastructure.
       (\<forall>aa::char list.
           (\<forall>(l::location) l'::location. aa @\<^bsub>graphI a\<^esub> l \<and> aa @\<^bsub>graphI a\<^esub> l' \<longrightarrow> l = l') \<and>
           (\<forall>l::location. nodup aa (agra (graphI a) l))) \<longrightarrow>
       (\<forall>aa::char list.
           (\<forall>(l::location) l'::location. aa @\<^bsub>graphI a\<^esub> l \<and> aa @\<^bsub>graphI a\<^esub> l' \<longrightarrow> l = l') \<and>
           (\<forall>l::location. nodup aa (agra (graphI a) l)))" by simp
  next show "\<And>(a::infrastructure) (b::infrastructure) (c::infrastructure).
       (a, b) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       (\<forall>aa::char list.
           (\<forall>(l::location) (l'::location). (aa @\<^bsub>graphI a\<^esub> l \<and> aa @\<^bsub>graphI a\<^esub> l') \<longrightarrow> l = l') \<and>
           (\<forall>l::location. nodup aa (agra (graphI a) l))) \<longrightarrow>
       (\<forall>a::char list.
           (\<forall>(l::location) (l'::location). (a @\<^bsub>graphI b\<^esub> l \<and> a @\<^bsub>graphI b\<^esub> l') \<longrightarrow> l = l') \<and>
           (\<forall>l::location. nodup a (agra (graphI b) l))) \<Longrightarrow>
       (b, c) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
       (\<forall>aa::char list.
           (\<forall>(l::location) l'::location. (aa @\<^bsub>graphI a\<^esub> l \<and> aa @\<^bsub>graphI a\<^esub> l') \<longrightarrow> l = l') \<and>
           (\<forall>l::location. nodup aa (agra (graphI a) l))) \<longrightarrow>
       (\<forall>a::char list.
           (\<forall>(l::location) l'::location. (a @\<^bsub>graphI c\<^esub> l \<and> a @\<^bsub>graphI c\<^esub> l') \<longrightarrow> l = l') \<and>
           (\<forall>l::location. nodup a (agra (graphI c) l)))"
      by (rule impI, rule allI, rule actors_unique_loc_base, drule CollectD, 
             simp,erule impE, assumption, erule spec)   
  qed
  show ?thesis 
  by (insert ind, insert assms(2), simp)
qed

lemma actors_unique_loc_aid_base:"
 \<forall> a. (\<forall> l l'. a @\<^bsub>graphI Airplane_not_in_danger_init\<^esub> l \<and> 
               a @\<^bsub>graphI Airplane_not_in_danger_init\<^esub> l' \<longrightarrow> l = l')\<and>
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
           a @\<^bsub>Lgraph {(cockpit, door), (door, cabin)}
                (\<lambda>x::location.
                    if x = cockpit then [''Bob'', ''Charly'']
                    else if x = door then [] else if x = cabin then [''Alice''] else [])
                ex_creds ex_locs\<^esub> l \<and>
           a @\<^bsub>Lgraph {(cockpit, door), (door, cabin)}
                (\<lambda>x::location.
                    if x = cockpit then [''Bob'', ''Charly'']
                    else if x = door then [] else if x = cabin then [''Alice''] else [])
                ex_creds ex_locs\<^esub> l' \<longrightarrow>
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
 \<Longrightarrow>     \<forall> a. (\<forall> l l'. a @\<^bsub>graphI I\<^esub> l \<and> a @\<^bsub>graphI I\<^esub> l' \<longrightarrow> l = l')\<and>
         (\<forall> l. nodup a (agra (graphI I) l))"  
  by (erule actors_unique_loc_step, rule actors_unique_loc_aid_base)
    
(* Using the state transition, Kripke structure and CTL, we can now
   also express (and prove!) unreachability properties which enable to 
   formally verify security properties for specific policies, like two-person
   rule. *)

lemma Anid_airplane_actors: "actors_graph (graphI Airplane_not_in_danger_init) = airplane_actors"
  apply (simp add: Airplane_not_in_danger_init_def ex_graph_def actors_graph_def nodes_def airplane_actors_def)
  apply (rule equalityI)
   apply (rule subsetI)
   apply (drule CollectD)
   apply (erule exE)
   apply (erule conjE)+
   apply (simp add: door_def cockpit_def cabin_def)
   apply (erule conjE)+
    apply force
  apply (rule subsetI)
  apply (rule CollectI)
       apply (simp add: door_def cockpit_def cabin_def)
  apply (case_tac "x = ''Bob''")
   apply force
      apply (case_tac "x = ''Charly''")
   apply force
  apply (subgoal_tac "x = ''Alice''")
   apply force
by simp    
   
(*later show that (Anid, I) \<in> {(x,y). x \<rightarrow> y}* \<longrightarrow> actors_graph Anid = actors_graph I 
  and also that   actors_graph Anid = airplane_actors and thus 
  (Anid, I) \<in> {(x,y). x \<rightarrow> y}* \<longrightarrow> actors_graph I  = airplane_actors and 
   since Eve \<notin> airplane_actors we have that Eve \<noteq> n and Eve \<noteq> a.
   In fact above actors_graph is not so important as intermediate step it
   is only important to have a fixed set for all I equal to actors_graph I since
   we can show that n and a are in actors_graph I (?). *)



(* Lemma to apply the previous stuff within the lemma below *)

lemma all_airplane_actors: "(Airplane_not_in_danger_init, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
              \<Longrightarrow> actors_graph(graphI y) = airplane_actors"
apply (insert Anid_airplane_actors)  
  apply (erule subst)  
    apply (rule sym)
by (erule same_actors)
      
lemma actors_at_loc_in_graph: "\<lbrakk> l \<in> nodes(graphI I); a  @\<^bsub>graphI I\<^esub> l\<rbrakk>
                                \<Longrightarrow> a \<in> actors_graph (graphI I)"
  apply (simp add: atI_def actors_graph_def)
  by (rule exI, rule conjI, assumption, assumption)
    
lemma not_en_get_Apnid: "(Airplane_not_in_danger_init,y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
         \<Longrightarrow> ~(enables y l (Actor a) get)"
  apply (subgoal_tac "delta y = delta(Airplane_not_in_danger_init)")
apply (simp add: Airplane_not_in_danger_init_def enables_def local_policies_four_eyes_def)    
  apply (rule sym)
    by (erule init_state_policy)
 
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

(* Comments of changes of tspace and lspace wrt earlier versions:
   Now tspace and lspace have a semantics based on the state i.e.
   the graph/infrastructure. Based on this semantics, we have definitions now 
   in AirInsider for 
   role(Actor x, r) and has(Actor y, c) as well as for locations
   for isin l s .  For example tspace (Actor a) does not return
   just bool as before but all roles and credentials that the actor has. A policy 
   would still state has (x,''PIN'') for example but the ex_creds map assigns a 
   pair of lists instead of bool. 
   Semantics of has is achieved by extending the type with infrastructure
   has :: [infrastructure, (actor *string)] \<Rightarrow> bool but with semantics
   "has I (a, c) == (a,c) \in credentials(tspace I a)
   where credential is an acronym for lambda lxl. set(first lxl)
   similar for role with projection roles lxl = set(snd lxl) 
   [infrastructure, (actor *string)] \<Rightarrow> bool where
   role I (a, r) == (a, r) \in roles(tspace I a)
   For lspace we define isin
   isin :: [infrastructure, location, string] \<Rightarrow> bool where
   isin I l s == (l,s) \in set(lspace I l) 
   we don't need projections here since lspace is just one table
   (i.e. list of pairs (location * string)).
*)    
    
(* Invariant: number of staff in cockpit never below 2 *)

lemma two_person_inv[rule_format]: "\<forall> z z'. (2::nat) \<le> length (agra (graphI z) cockpit) \<and> 
                          nodes(graphI z) = nodes(graphI Airplane_not_in_danger_init) \<and>
                          delta(z) = delta(Airplane_not_in_danger_init) \<and>
                          (Airplane_not_in_danger_init,z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<and>
                           z \<rightarrow>\<^sub>n z' \<longrightarrow> (2::nat) \<le> length (agra (graphI z') cockpit)"
  apply clarify
  apply (erule state_transition_in.cases)
    defer
     apply simp+
     apply (simp add: move_graph_a_def)
  apply (rule conjI)
   prefer 2
   apply clarify
   apply simp
  apply clarify
  apply (subgoal_tac "l' = door \<or> l' = cabin")
   prefer 2
   apply (simp add: Airplane_not_in_danger_init_def nodes_def ex_graph_def)
   apply blast
      apply (erule disjE)
 (* show  (3::nat) \<le> length (lgra (graphI I) cockpit) from enables I l' (Actor a) move for 
    l' = door *)    
   apply (subgoal_tac "(3::nat) \<le> length (agra (graphI I) cockpit)")
   apply (simp add: del_sort)
   apply (simp add: enables_def local_policies_four_eyes_def Airplane_not_in_danger_init_def ex_graph_def nodes_def)
 (* l' = cabin: move from cockpit should not be possible because the way the policy is defined *)
   apply (simp add: enables_def Airplane_not_in_danger_init_def)
  apply (erule bexE)
  apply (simp add: local_policies_four_eyes_def cabin_def door_def)
    (* 1.9. 2017:
       Need an invariant that Actor a can only be at one location. This can be proved
       for a sensible state and its descendants like Airplane_not_in_danger. Here it 
       can be used to show contradiction between 
        \<exists>n::char list. n @\<^bsub>graphI I\<^esub> Location (Suc (0::nat)) \<and> Actor n = Actor a 
        and a \<in> set (agra (graphI I) cockpit)  
        7.9.2017
        A first investigation shows a problem:
        Actor a = Actor b possible even if a \<noteq> b (Actor not injective on all inputs)
        Therefore, the above is not sufficient for a contradiction.
        We may be able to show an invariant like
        \<forall> G l. a @\<^bsub>G\<^esub> l \<and> a @\<^bsub>G\<^esub> l' \<Longrightarrow> l = l' , i.e. inj (\<lambda> l. a @\<^bsub>G\<^esub> l) (1)
        but this is on identities (strings) a not Actors!
        The state_transition uses move_graph_a on the identities that are stored
        at nodes in the graph and not Actors precisely because Actor isn't injective.
        Therefore a move_graph_a on Actors instead identities would have to have a 
        mechanism to make sure all copies of equal Actor-values for different identities 
        are moved from various different nodes in a step. This is not easily computable
        and would make the step relation quite complex.
        The overall design of the model is that the graph has the real identities
        and the Actor adds a layer of impersonation that could be faked precisely
        for the insider case.
        However, we do assume that Insider ''Eve'' {''Charly''} and tipping_point ''Eve''
        which implies UasI ''Eve'' ''Charly'' meaning that
        Actor ''Eve'' = Actor ''Charly''\<and> 
        \<forall> x y. x \<noteq>''Eve''\<and> y \<noteq>''Charly''\<and> Actor x = Actor y \<longrightarrow> x = y
        Now, we could extend the UasI definition such that UasI ''Eve'' ''Charly'' means
         \<forall> G l. ''Eve''  @\<^bsub>G\<^esub> l = ''Charly''  @\<^bsub>G\<^esub> l 
        but that would actually be an inconsistent assumption (in the existing state_transition)
        since ''Eve'' and ''Charly'' could move by state_transition to different locations
        (then contradicting this additional assumption). 
        
        But if we keep the Insider assumption for ''Eve'' and ''Charly'' as is we do 
        have that \<forall> x y. x \<noteq>''Eve''\<and> y \<noteq>''Eve'' \<and> Actor x = Actor y \<longrightarrow> x = y
        so that for those case we could derive a contradiction in the above situation
        needed in the lemma if we can show that n \<noteq> ''Eve'' and a \<noteq> ''Eve'' 
        because then we can get from Actor n = Actor a that n = a.
        We still need the lemma (1) above to get the contradiction to 
        n @\<^bsub>G\<^esub> door and a @\<^bsub>G\<^esub> cockpit and door \<noteq> cockpit.
        (It's an invariant, i.e. we need to show that it's preserved by \<rightarrow>i and
         that if it holds for x and x \<rightarrow>i* y then it also holds for y so we can
         then show this invariant for a state that comes from some initial state
         like Airplane_not_in_danger where invariant holds)
       Now, we still need to get n \<noteq> ''Eve'' and a \<noteq> ''Eve'': the latter could be 
       derived from showing showing that a \<in> airplane_actors which follows from
        a @\<^bsub>graphI I\<^esub> cockpit and similarly  n \<noteq> ''Eve''from n @\<^bsub>graphI I\<^esub> door 
      by using another invariant ~ (''Eve'' @\<^bsub>graphI I'\<^esub> l) \<forall> l \<in> nodes (graphI I')
      if I \<rightarrow>i* I'  und ~(''Eve'' @\<^bsub>graphI I'\<^esub> l) \<forall> l \<in> (nodes (graphI I)).

      It might seem a bit dodgy to prove all these strong safety ad security statements
      based on the assumption that Eve is never in the airplane but the insiderness
      still allows Eve to control Charly. 

12.10.2017:
We cannot show that Air_tp_Kripke \<turnstile> AG ({x. global_policy x ''Eve''})"
because \<not> enables z cockpit (Actor ''Eve'') put
is not given in all states reachable from Airplane_not_in_danger_init:
since we have the Insider assumption, at any point in time Actor Charly
can be replaced by Actor Eve and since Actor Charly can execute action 
put in location cockpit so can Actor Eve. 
This is the whole point of the Insider framework, that the impersonation
at the Actor level enables the Insider to act instead of the alter ego.
Nevertheless, we can prove the 2 person invariant; we can also simply prove
that Eve is never in the cockpit: AG({x. ~(''Eve'' @\<^bsub>graphI x\<^esub> cockpit)})
(simply because ''Eve'' is never in the Airplane for states derived from
Airplane_not_in_danger_init),
What is revealed by this exercise is that clearly we cannot disprove what
we have proved before: an Insider attack is possible if the Insider is
in the cockpit. What we might hope to achieve -- and this is what the
failed naive attempt shows -- is to establish a new locale assumption
fixes foe_control :: "[location, actor] \<Rightarrow> bool"
defines foe_control_def: "foe_control l a \<equiv>  
   ! I:: infrastructure. (? x :: identity. 
        x @\<^bsub>graphI I\<^esub> l \<and> Actor x \<noteq> Actor ''Eve'')
             \<longrightarrow> ~ (enables I l (Actor ''Eve'') a)"
assumes cockpit_foe_control: "foe_control cockpit put"

From the two_person_invariant for all I 
(2::nat) \<le> length (agra (graphI I) cockpit)  
we can infer that
(? x :: identity. 
        x @\<^bsub>graphI I\<^esub> l \<and> Actor x \<noteq> Actor ''Eve'')
because only Actor ''Charly'' = Actor ''Eve''
so there must be another one. Therefore the
foe_control applies and we can show that 
Actor Eve cannot execute action put in cockpit. 
In fact, this contradicts the Insider assumption. In other words
we can derive Actor Eve can put in cockpit and that he cannot!
*)
    
  apply (erule exE)
  apply (subgoal_tac "n \<noteq> ''Eve''")
   apply (subgoal_tac "a \<noteq> ''Eve''")
    apply (subgoal_tac "a = n")
     apply (subgoal_tac "n \<in> set (agra (graphI I) cockpit)")
      apply (subgoal_tac "cockpit = door")
       apply (simp add: cockpit_def door_def)
      apply (fold Airplane_not_in_danger_init_def)
      apply (drule actors_unique_loc_aid_step)
      apply (drule_tac x = a in spec,erule conjE,
             drule_tac x = cockpit in spec, drule_tac x = door in spec, 
             erule impE, simp add: door_def)
      apply assumption
     apply (erule subst, assumption)
    apply (insert Insider_Eve)
apply (unfold Insider_def)
apply ((drule mp), rule Eve_precipitating_event)
    apply (simp add: UasI_def)
    (* a \<noteq> Eve *)
   apply (simp add: actors_graph_def)
   apply (subgoal_tac "a \<in> airplane_actors")
    apply (simp add: airplane_actors_def)
    apply force
    apply (subgoal_tac "cockpit \<in> nodes(graphI I)")
    apply (subgoal_tac "a \<in> actors_graph (graphI I)")
     apply (drule all_airplane_actors)
     apply (erule subst, assumption)
    apply (erule actors_at_loc_in_graph)
  apply (simp add: atI_def)
   apply (drule same_nodes)
   apply (rotate_tac -1)
   apply (erule ssubst)
    apply (simp add: Airplane_not_in_danger_init_def) 
 (* n \<noteq> Eve *)
       apply (simp add: actors_graph_def)
   apply (subgoal_tac "n \<in> airplane_actors")
    apply (simp add: airplane_actors_def)
    apply force
    apply (subgoal_tac "door \<in> nodes(graphI I)")
    apply (subgoal_tac "n \<in> actors_graph (graphI I)")
     apply (drule all_airplane_actors)
     apply (erule subst, assumption)
    apply (erule actors_at_loc_in_graph)
  apply (simp add: atI_def door_def)
   apply (drule same_nodes)
   apply (rotate_tac -1)
   apply (erule ssubst)
  apply (simp add: Airplane_not_in_danger_init_def ex_graph_def nodes_def door_def) 
by blast
    
  
lemma two_person_inv1[rule_format]: "(Airplane_not_in_danger_init,z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
                           \<Longrightarrow> (2::nat) \<le> length (agra (graphI z) cockpit)"  
  apply (rule mp)
  prefer 2
   apply assumption
     apply (erule rtrancl_induct)  
   apply (rule impI)
apply (simp add: Airplane_not_in_danger_init_def ex_graph_def)    
  apply (rule impI)
  apply (rule_tac z = y in two_person_inv)
  apply (rule conjI)
   apply (erule impE)
    apply assumption+
  apply (rule conjI)
   apply (rule same_nodes, assumption)
  apply (rule conjI)
    apply (rule sym)
   apply (rule init_state_policy, assumption)
    apply (erule conjI)
    by simp
     
(* set version should also work*)
(* The version of two_person_inv above we need, uses cardinality of lists of 
   actors rather than length of lists. Therefore first some equivalences
   and then a restatement of two_person_inv *)   
(* proof idea: show since there are no duplicates in the list
    agra (graphI z) cockpit therefore then 
         card(set(agra (graphI z))) = length(agra (graphI z)) *)
lemma nodup_card_insert: 
       "a \<notin> set l \<longrightarrow> card (insert a (set l)) = Suc (card (set l))"      
by auto
       
lemma no_dup_set_list_num_eq[rule_format]: 
    "(\<forall> a. nodup a l) \<longrightarrow> card (set l) = length l" 
     apply (induct_tac l) 
   apply (simp)
    apply clarify
  apply simp
  apply (erule impE)
  prefer 2
   apply assumption
  apply (rule allI)
    apply (drule_tac x = aa in spec)
  apply (case_tac "a = aa")
   apply simp
   apply (erule nodup_notin)
by simp
    
lemma two_person_set_inv[rule_format]: "(Airplane_not_in_danger_init,z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
                           \<Longrightarrow> (2::nat) \<le> card (set (agra (graphI z) cockpit))"  
  apply (subgoal_tac "card (set (agra (graphI z) cockpit)) = length(agra (graphI z) cockpit)")
   apply (erule ssubst, rule two_person_inv1)
   apply assumption
  apply (rule no_dup_set_list_num_eq)
  apply (drule actors_unique_loc_aid_step)
  apply (drule_tac x = a in spec)
  apply (erule conjE)
    apply (rotate_tac -1)
  by (erule_tac x = cockpit in spec)
        
lemma Pred_all_unique: "\<And> P. (\<lbrakk> \<forall> x. (P x \<longrightarrow> (x = c)) \<rbrakk>  \<Longrightarrow> P c)"
  apply (case_tac "P c")
apply (drule spec)
  oops
    
lemma Pred_all_unique: "\<lbrakk> ? x. P x; (! x. P x \<longrightarrow> x = c)\<rbrakk> \<Longrightarrow> P c"
  apply (case_tac "P c")
   apply assumption
  apply (erule exE)
  apply (drule_tac x = x in spec)
  apply (drule mp)
   apply assumption
    by (erule subst, assumption) 
              
lemma Set_all_unique: "\<lbrakk> S \<noteq> {}; (\<forall> x \<in> S. x = c) \<rbrakk> \<Longrightarrow> c \<in> S"
  apply (rule_tac P = "\<lambda> x. x \<in> S" in Pred_all_unique)
   apply force
  by simp
    
lemma airplane_actors_inv0[rule_format]: 
    "\<forall> z z'. (\<forall>h::char list \<in> set (agra (graphI z) cockpit). h \<in> airplane_actors) \<and> 
          (Airplane_not_in_danger_init,z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<and>
            z \<rightarrow>\<^sub>n z' \<longrightarrow>  (\<forall>h::char list\<in>set (agra (graphI z') cockpit). h \<in> airplane_actors)"     
  apply clarify
  apply (erule state_transition_in.cases)
    defer
     apply (simp)+
  apply (simp add: move_graph_a_def)
  apply (case_tac "a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')")
   apply simp
   defer
     apply simp
   apply (case_tac "l' = cockpit")
   apply simp
   prefer 2
   apply simp
   apply (case_tac "cockpit = l")
    prefer 2
    apply simp+
   apply (erule bspec)
   apply (erule del_up)
    apply (erule disjE)
   prefer 2
      apply (erule bspec)
   apply assumption
  apply (subgoal_tac "delta(I) = delta(Airplane_not_in_danger_init)")
   apply (simp add: enables_def)
   apply (erule bexE)
   apply (simp add: Airplane_not_in_danger_init_def)
   prefer 2
  apply (rule sym)
    apply (erule init_state_policy)
  apply (unfold local_policies_four_eyes_def)
  apply simp
  apply (erule disjE)
   apply simp+
 (* same trick as above show what Eve is not in the graph *)  
  apply (erule exE)
  apply (erule conjE)+  
  apply (fold local_policies_four_eyes_def Airplane_not_in_danger_init_def)
  apply (drule all_airplane_actors)
    by (erule subst)
 
lemma airplane_actors_inv: "(Airplane_not_in_danger_init,z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
                           \<Longrightarrow>  \<forall>h::char list\<in>set (agra (graphI z) cockpit). h \<in> airplane_actors"     
      apply (rule mp)
  prefer 2
   apply assumption
     apply (erule rtrancl_induct)  
   apply (rule impI)
    apply (rule ballI)
apply (simp add: Airplane_not_in_danger_init_def ex_graph_def airplane_actors_def ex_locs_def)    
apply blast
   apply (rule impI)
    apply (rule ballI)
    apply (rule_tac z = y in airplane_actors_inv0)
   apply (rule conjI)
    apply (erule impE)
     apply assumption+
   apply simp
    by assumption

    
lemma Eve_not_in_cockpit: "(Airplane_not_in_danger_init, I)
       \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       x \<in> set (agra (graphI I) cockpit) \<Longrightarrow> x \<noteq> ''Eve''"
  apply (drule airplane_actors_inv)
  apply (simp add: airplane_actors_def)
  apply (drule_tac x = x in bspec, assumption)
    by force
    
(* 2 person invariant implies that there is always some x in cockpit x \<noteq> Eve *)      
lemma tp_imp_control: "(Airplane_not_in_danger_init,I) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
        \<Longrightarrow>  (? x :: identity.  x @\<^bsub>graphI I\<^esub> cockpit \<and> Actor x \<noteq> Actor ''Eve'')"
  apply (frule two_person_set_inv)
    apply (unfold atI_def)
  apply (subgoal_tac 
         "\<not>(\<forall> x \<in> set(agra (graphI I) cockpit). (Actor x = Actor ''Eve''))")
   apply blast
  apply (rule notI)
  apply (subgoal_tac "\<forall>x::char list\<in>set (agra (graphI I) cockpit). x = ''Charly''")
   apply (subgoal_tac "set (agra (graphI I) cockpit) = {''Charly''}")
    apply (subgoal_tac 
       "(card((set (agra (graphI I) cockpit)) :: char list set)) = (1 :: nat)")
     apply (subgoal_tac "(2 :: nat) \<le> (1 ::nat)")
      apply arith
     apply (erule subst, assumption)
    apply (subgoal_tac "is_singleton({''Charly''})") 
    thm is_singleton_altdef
       apply (unfold is_singleton_altdef)
       apply (rule ssubst, assumption, assumption)
      apply (fold is_singleton_altdef)
      apply (rule is_singletonI)
     apply (rule equalityI)
      apply (rule subsetI)
      apply simp
     apply (rule subsetI)
     apply simp
     apply (rule Set_all_unique)
      apply force
     apply assumption
       apply (rule ballI)
    apply (drule_tac x = x in bspec)
     apply assumption
    apply (subgoal_tac "x \<noteq> ''Eve''")
     apply (insert Insider_Eve)
     apply (unfold Insider_def)
       apply ((drule mp), rule Eve_precipitating_event)
     apply (simp add: UasI_def)
    by (erule Eve_not_in_cockpit)
  
lemma Fend_2:    "(Airplane_not_in_danger_init,I) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
         \<not> enables I cockpit (Actor ''Eve'') put"
      apply (insert cockpit_foe_control)
  apply (simp add: foe_control_def)
  apply (drule_tac x = I in spec)
  apply (erule mp)
  by (erule tp_imp_control)
    
theorem Four_eyes_no_danger: "Air_tp_Kripke \<turnstile> AG ({x. global_policy x ''Eve''})"
  apply (simp add: Air_tp_Kripke_def check_def)
  apply (rule conjI)
   apply (simp add: Airplane_not_in_danger_init_def Air_tp_states_def
                    state_transition_in_refl_def)
(*  apply (rule conjI) *)
   apply (unfold AG_def)
   apply (simp add: gfp_def)
    apply (rule_tac x = "{(x :: infrastructure) \<in> states Air_tp_Kripke. ~(''Eve'' @\<^bsub>graphI x\<^esub> cockpit)}" in exI)
    apply (rule conjI)
    apply (unfold global_policy_def)
    apply (simp add: airplane_actors_def)
    apply (rule subsetI)
    apply (drule CollectD)
    apply (rule CollectI)
    apply (erule conjE)
      apply (simp add: Air_tp_Kripke_def Air_tp_states_def state_transition_in_refl_def)
    apply (erule Fend_2)
       apply (rule conjI)
    apply (rule subsetI)
    apply (simp add: AX_def)
    apply (rule subsetI)
    apply (rule CollectI)
    prefer 2
    apply (simp add: Airplane_not_in_danger_init_def Air_tp_Kripke_def)
    apply (rule conjI)
    apply (simp add: Air_tp_states_def)
     apply (simp add: Airplane_not_in_danger_init_def state_transition_refl_def)
    apply (simp add: ex_graph_def atI_def)
(*   apply (rule conjI)
    apply (erule conjE) *)
    apply (simp add:  Air_tp_Kripke_def Air_tp_states_def state_transition_in_refl_def)
   apply (simp add: ex_graph_def atI_def)
    apply (simp add:  Air_tp_Kripke_def Air_tp_states_def state_transition_in_refl_def)
  apply (rule conjI)
 (*         apply (rule rtrancl_trans)
       apply assumption
      apply blast *)
    apply (subgoal_tac "(Airplane_not_in_danger_init, xa)
       \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*")
    apply (simp add: atI_def)
   apply (erule conjE)
  apply (unfold state_transition_infra_def state_transition_in_refl_def)
   apply (erule rtrancl_into_rtrancl)
   apply (rule CollectI)
   apply simp
(* remaining case (apart from L Airplane_not_in_danger_init): ...
       isin cockpit ''air'' \<Longrightarrow>
       x \<in> states Air_tp_Kripke \<and> \<not> ''Eve'' @\<^bsub>graphI x\<^esub> cockpit \<Longrightarrow>
       xa \<in> Collect (state_transition x) \<Longrightarrow> \<not> ''Eve'' @\<^bsub>graphI xa\<^esub> cockpit *)
    apply (subgoal_tac "(Airplane_not_in_danger_init, xa)
       \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*")
  apply (rule notI)
  apply (simp add: atI_def)
  apply (erule conjE)
apply (drule Eve_not_in_cockpit)
    apply assumption
   apply simp
  apply (rule rtrancl_trans)
  apply (erule conjE)
       apply assumption
by blast


end
  
  
  
(* Original conjecture that lead to the final lemmas on AG : 
Zwei etwas gewagte Ansatzpunkte, die ich aber gerne mal untersuchen wuerde:
- Kann man zeigen, dass die Tuer so sein muss wie sie ist, i.e. wenn man 
  eine Terrorsicherung haben will, dann muss sie von innen definitiv veriegelbar 
  sein.
- Kann man zeigen, dass wenn ein zweiter im Cockpit ist und er staerker ist als 
  der Pilot, dass dann auch ein Insider keine Gefahr darstellt? 
  (Kommentar: das ist falsch formuliert "staerker als der Pilot": jeder der 
   beiden muss in der Lage sein den anderen von gefaehrlichen Aktionen abzuhalten
   (mindestens das Flugzeug zum Absturz zu bringen))
(Translation: 
"Two rather daring starting points, that I'd like to investigate eventually:
- it it possibly to show that the door has to be as it is, that is, if we want a
  terror protection, it must be lockable from inside.
- can we show that if a second person is in the cockpit and he is stronger than the
  pilot, that in this case even an insider represents no danger? )
  (comment: that is phrased wrongly "stonger than the pilot": each of the
   two must be in a position to prevent the other from dangerous actions (at
   least from bringing down the airplane)"

<20.10.19< The former point is contained in the property Security
<20.10.19< The last point has become obsolete by the previous development, i.e., we
   need to make precisely the assumption that the second person can overcome the insider.
 
Wenn man diese zwei Punkte logisch ausdruecken kann und am Modell beweisen
kann, waere das ein Schritt vorwaerts.
*)
  
end
    
    
