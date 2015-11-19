(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * SteamDat.thy --- 
 * This file is part of HOL-Z.
 *
 * Copyright (c) 1998-2000 GMD First, Germany
 *               2000-2003 University Freiburg, Germany
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
(* $Id: SteamDat.thy 6741 2007-08-03 06:20:19Z brucker $ *)

(************************************************************************)
(* Es ist nicht die vollstaendige Spezifikation, stellt aber alle fuer  *)
(* die Repraesentation der Schema: STEAM_BOILER_WAITING und             *) 
(* STEAM_REPAIRED erforderlichen Definitionen zur Verfuegung.           *)
(************************************************************************)

SteamDat = Z +

schemas 
   PhysModes     ::= waiting | adjusting | ready | running | stopped
   Alarm         ::= ON | OFF
   UnitStates    ::= working | broken | closed  | 
                     opening  | open  | flow  | noflow 

"SensorStates == {working, broken}" 

(*
  C           : capacity of the tank  (l)
  W           : maximal steam output  (l/s)
  U1          : max decrease of the steam output (l/s^2)
  U2          : max. increase of the steam output (l/s^2)
  NP          : number of pumps
  P           : pump throughput (l/s)
  pump_delay  : punp starting time (s)
  T           : sampling rate
  M1,M2,N1,N2 : absolut and normal water level limits (l)
*)

"+..
    C   : %N;
    W   : %N;
    U1  : %N;
    U2  : %N;
    P   : %N;
    NP  : %N;
    T   : %N;
    pump_delay : %N;
    M1  : %N;
    M2  : %N;
    N1  : %N;
    N2  : %N
 |--
    #0 <= M1 & M1 <= N1 & N1 <= N2 & N2 <= M2 & M2 <= C &   
    NP = #4 & T = pump_delay & pump_delay = #5 &
    T * NP * P < N2 - N1 & T * W < N2 - N1
 -.. "  


constdefs get_pst :: "'a * 'b * 'c * 'd => 'a"
          "get_pst == (%(pst,pa2,pa1,mst).(pst))"
          get_pa1 :: "'a * 'b * 'c * 'd => 'c"
          "get_pa1 == (%(pst,pa2,pa1,mst).(pa1))"
          get_pa2 :: "'a * 'b * 'c * 'd => 'b"
          "get_pa2 == (%(pst,pa2,pa1,mst).(pa2))"
          get_mst :: "'a * 'b * 'c * 'd => 'd"
          "get_mst == (%(pst,pa2,pa1,mst).(mst))" 

  
end
