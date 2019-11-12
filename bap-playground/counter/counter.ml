(* Yihao Sun "ysun67@syr.edu"
   2019 in Syracuse

   this is counter plugin to count how many "JMP" expr in deasmed
   IR *)

open Core_kernel
open Bap.Std
open Format


include Self()

let counter = object
  inherit [int] Term.visitor
  method! enter_term _ _ num = num + 1
end

(** try to directly visit IL 
    disasm can turn a program into BIL(in a lazy sequence)*)
let countp proj =
  let instructions = Disasm.insns (Project.disasm proj) in
  let is_jump men_i_tuple =
    match men_i_tuple with
    (* using modal properties of Ins *)
    | (mem, i) ->
      if Insn.is Insn.jump i
      then (printf "hit jump instr %a \n" Insn.pp_adt i; true)
      else false in
  let count_jmp ins = Seq.count ins is_jump in
  count_jmp instructions

let main proj =
  let term_num = countp proj in
  printf "there are %d terms in program" term_num

let () = Project.register_pass' main
