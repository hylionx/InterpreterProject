let apply_hoare_tactic (tactic : tactic) (goal :goal) =
  match goal.conclusion with
  | LogicForm(prop) -> apply_prop_tactic tactic goal
  | Hoare(h) ->
     match tactic with
     | HSkip -> if h.program == Skip
                   && (h.precondition == h.precondition)
                then []
                else failwith "the HSkip tactic does not apply"
     | HAssign -> (match h.program with
                  | Affect(c, v) ->
                     let tmp = psubst c v h.postcondition in
                       if tmp == h.precondition
                       then []
                       else [goal]
                  | _ -> failwith "the HAssign tactic does not apply")
     | HIf -> (match h.program with
               | Condition(b, p1, p2) -> [{ context = goal.context;
                                            conclusion = Hoare({precondition =  bool2prop b; program = p1; postcondition = h.postcondition});};
                                          { context = goal.context;
                                            conclusion = Hoare({precondition = bool2prop (Not b); program = p2; postcondition = h.postcondition});}]
               | _ -> failwith "the HIf tactic does not apply")
     | HRepeat(var) -> (match h.program with
                       | Repeat(v, p) -> let newprecondition = And(h.precondition, SmallerThan(Var var, v)) and
                                             newprogram = Sequence(Affect(var, Plus(Var var, Const 1)), h.program) and
                                             newpostcondition = h.precondition in
                                         [{context = goal.context;
                                           conclusion = Hoare({
                                                              precondition = newprecondition;
                                                              program = newprogram;
                                                              postcondition = newpostcondition;
                                         })}]
                       | _ -> failwith "the HRepeat tactic does not apply")
     | HCons(p1, p2) -> [
         {context = goal.context;
          conclusion = LogicForm(Implies(h.precondition, p1))};
         {context = goal.context;
          conclusion = LogicForm(Implies(p2, h.postcondition))};
         {context = goal.context;
          conclusion = Hoare({
                             precondition = p1;
                             program = h.program;
                             postcondition = p2})}]
     | HSEq(p) -> (match h.program with
                  | Sequence(p1, p2) -> [
                      {context = goal.context;
                       conclusion = Hoare({ precondition = h.precondition;
                                            program = p1;
                                            postcondition = p})};
                      {context = goal.context;
                       conclusion = Hoare({ precondition = p;
                                            program = p2;
                                            postcondition = h.postcondition})}]
                  | _ -> failwith "the HSEq tactic does not apply")
     | _ -> []
;;


let apply_tactic (t : tactic) (g : goal) : goal list =