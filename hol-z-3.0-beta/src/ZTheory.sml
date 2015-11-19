(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * ZTheory.sml --- 
 * This file is part of HOL-Z.
 *
 * Copyright (c) 2003-2007 ETH Zurich, Switzerland
 *
 * HOL-Z is free software; you can redistribute it and/or modify it under   
 * the terms of the GNU General Public License as published by the Free       
 * Software Foundation; either version 2 of the License, or (at your option)  
 * any later version.                                                         
 *                                                                            
 * HOL-Z is distributed in the hope that it will be useful, but WITHOUT ANY 
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS 
 * FOR A PARTICULAR PURPOSE. See the GNU General Public License for more 
 * details.                                                              
 *                                                                            
 * You should have received a copy of the GNU General Public License along    
 * with this program; if not, write to the Free Software Foundation, Inc.,    
 * 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.                  
 ******************************************************************************)
(* $Id: ZTheory.sml 6729 2007-08-03 05:25:17Z brucker $ *)

 
signature ZTHEORY =
  sig

  type  ztheory  

  exception IS_NOT_ZTHY of string

  val get_zenv           : ztheory -> ZEnv.Zenv
  val put_zenv           : ZEnv.Zenv -> theory -> ztheory

  val ZEnv_setup         : (theory -> theory) list

  val Add_TC             : thm list -> ztheory -> ztheory  
  val Del_TC             : thm list -> ztheory -> ztheory  
  val print_TC           : ztheory  -> unit

end;



structure ZTheory : ZTHEORY = 
struct

   structure ZEnvData : THEORY_DATA_ARGS =
   struct
     val name = "zenvironment" 
     type T = ZEnv.Zenv
     val empty = ZEnv.mt_zenv
     fun copy T = T
     fun prep_ext T = T
     fun extend T = T
     val merge  = (fn pp =>  ZEnv.merge)

     fun print thy T = ZEnv.prinzenv T
   end;

   structure ZEnv_DataManagement = TheoryDataFun(ZEnvData);
   val ZEnv_setup = [ZEnv_DataManagement.init]

   type      ztheory = theory

   exception IS_NOT_ZTHY of string;

   fun get_zenv thy = ZEnv_DataManagement.get thy 
                      handle _ => raise IS_NOT_ZTHY "NOT A Z THEORY";

   val put_zenv = ZEnv_DataManagement.put;


   fun Add_TC tc thy = 
       let val zenv = get_zenv thy
           val tc'  = (ZEnv.tc_simps_of zenv) addsimps tc
       in  put_zenv (ZEnv.update_Zenv_by_tc_simps zenv tc') thy
       end

   fun Del_TC  tc thy = 
       let val zenv = get_zenv thy
           val tc'  = (ZEnv.tc_simps_of zenv) delsimps tc
       in  put_zenv (ZEnv.update_Zenv_by_tc_simps zenv tc') thy
       end;

   fun print_TC thy = 
       let val zenv = get_zenv thy
       in  print_ss(tc_simps_of zenv) end

end;
