(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * Steam.thy --- 
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
(* $Id: Steam.thy 6741 2007-08-03 06:20:19Z brucker $ *)

(************************************************************************)
(* Es ist nicht die vollstaendige Spezifikation, stellt aber alle fuer  *)
(* die Repraesentation der Schema: STEAM_BOILER_WAITING und             *) 
(* STEAM_REPAIRED erforderlichen Definitionen zur Verfuegung.           *)
(************************************************************************)

Steam = Z + SteamDat + 


  
schemas
   

"
+-- WaterSensorModel ---
         qst : SensorStates; 
         qa1 : %N;
         qa2 : %N 
|--                                  
         #0 <= qa1  /\\
         qa1 <= qa2 /\\   
         qa2 <= C 
---
"

"+-- WaterSensorInit ---
         WaterSensorModel'
 |--
         qst' = working /\\
         qa1' = #0      /\\
         qa2' = C
 ---
"

"+-- WaterSensorWorking --- WaterSensorModel |-- qst = working ---"

"+-- WaterTolerable     --- WaterSensorModel |-- M1 <= qa1 /\\ qa2 <= M2---"

"+-- WaterAboveNormal   --- WaterSensorModel |-- N2 < qa2  ---"

"+-- WaterBelowNormal   --- WaterSensorModel |-- qa1 < N1  ---"

"+-- WaterNormal       ---  WaterSensorModel |-- N1 <= qa1 /\\ qa2 <= N2 ---" 

 
"
+-- SteamSensorModel  --- 
        vst : SensorStates; 
        va1 : %N; 
        va2 : %N
|--                                  
        #0 <= va1  /\\  
        va1 <= va2 /\\  
        va2 <= W  
---
"


"
+-- SteamZero ---
       SteamSensorModel; 
       va1 : %N
|--       
       va1 = #0 
---
"

"
+-- SteamSensorWorking --- 
        SteamSensorModel;
        vst : SensorStates 
|--       
        vst = working
 ---
"

"ValveStates == {open,closed}"

"+-- ValveModel  ---  vlv: ValveStates |-- True         ---"
"+-- ValveClosed ---  ValveModel       |-- vlv = closed ---"
"+-- ValveOpen   ---  ValveModel       |-- vlv = open   ---"
 

"PumpStates == {closed,opening,open,broken}"
 
"
+-- PumpModel ---     
       pst : PumpStates;
       pa1 : %N;
       pa2 : %N
|--
       pa1 <= pa2 /\\
       pst:{closed,opening} --> pa1=#0 /\\ pa2=#0 /\\
       pst = open --> pa1 = P /\\ pa2 = P
---
"

"MonitorStates == {flow, noflow, broken}" 

"
+-- MonitoredPumpModel ---   
       PumpModel; 
       mst : MonitorStates
|--                                   
       pst = broken         --> mst=flow   --> pa1 = P  /\\ pa2 = P   /\\
                                mst=noflow --> pa1 = #0 /\\ pa2 = #0  /\\
                                mst=broken --> pa1 = #0 /\\ pa2 = P   /\\

       pst:{closed,opening} --> mst:{noflow,broken}     /\\

       pst = open --> mst : {flow,broken}
---
"   


"
+-- Modes ---  
       st : PhysModes;
       alarm : Alarm
|--
       st = stopped --> alarm = ON
---
"

"
+-- MonitoredPumpsModel ---
       Ps  : seq MonitoredPumpModel;
       pa1 : %Z;
       pa2 : %Z
|-- 
       #Ps = NP /\\
       pa1 = P * (#{i.((i : (#1..NP)) /\\ (get_pa1(Ps %^ i) = P))}) /\\
       pa2 = P * (#{i.((i : (#1..NP)) /\\ ((PROJ(Ps %^ i)get_pa2 ''pa2'') = P))}) 
---
"



"+-- ActorModels --- MonitoredPumpsModel;vlv:ValveStates |-- ValveModel---"

"SensorModels == (WaterSensorModel /\\ SteamSensorModel)"                                 
(*
"UnitModels   == (SensorModels /\\ ActorModels)"
*)

"
+--PumpsOpen---
     MonitoredPumpsModel
|--  ALL i: (#1 .. NP). (PROJ(Ps %^ i)get_mst ''mst'') ~= broken
                        --> (PROJ(Ps %^ i)get_mst ''mst'') = open
---
"

"
+-- PumpsClosed ---
      MonitoredPumpsModel   
|--   ALL i: (#1 .. NP). (PROJ(Ps %^ i)get_mst ''mst'') ~= broken 
                                     --> (PROJ(Ps %^ i)get_mst ''mst'') = closed
---
"

  
"
+-- PumpsWorking ---  
      MonitoredPumpsModel
|--   ALL i: (#1 .. NP). (PROJ(Ps %^ i)get_mst ''mst'') ~= broken
---
"


"
+-- PumpControlsWorking---
      MonitoredPumpsModel
|--   ALL i: (#1 .. NP). (PROJ(Ps %^ i)get_pst ''pst'') ~= broken
---
"
   
  
"NoDefects       == (WaterSensorWorking /\\ SteamSensorWorking /\\ 
                     PumpsWorking       /\\ PumpControlsWorking)"                                    

"TolerableDefects == (WaterSensorWorking \\/ 
                     (SteamSensorWorking /\\ PumpControlsWorking))"  

 
"
+-- SteamBoiler ---
       WaterSensorModel;
       SteamSensorModel;
       MonitoredPumpsModel;
       ValveModel;
       Modes
|--
       st:{waiting,adjusting,ready} --> alarm = OFF
                             <->  NoDefects /\\ SteamZero            /\\
       st = running                 --> alarm = OFF 
                             <-> WaterTolerable /\\ TolerableDefects /\\
       st = running | PumpsOpen    --> ValveClosed
---
" 


"+-- DataTransmission--- %Delta SteamBoiler |-- st' = st /\\ alarm = OFF ---"



"
+-- LEVEL_REPAIRED ---
       %Delta SteamBoiler;
       %Xi SteamSensorModel;
       %Xi ActorModels
|--
       alarm = OFF      /\\
       (qst = broken    /\\ st' = st)       \\/ 
       qst ~= broken    /\\ st' = stopped   /\\
       qst' = working   /\\ (qa1',qa2') = (qa1,qa2) 
 ---
"


"
+-- STEAM_REPAIRED ---  
       %Delta SteamBoiler;
       %Xi WaterSensorModel;
       %Xi ActorModels
|--
       alarm = OFF     /\\
       (vst = broken   /\\ st' = st)     \\/ 
       vst ~= broken   /\\ st' = stopped /\\
       vst' = working  /\\ (va1',va2') = (va1,va2) 
---
"


"
+-- PUMP_CONTROL_REPAIRED --- 
       %Delta SteamBoiler; 
       %Xi SensorModels;
       %Xi ValveModel;
       i : (#1 .. NP)
|--
       alarm = OFF /\\
       ((PROJ(Ps %^ i)get_pst ''pst'')  = broken  /\\ st' = st) \\/   
       (~(PROJ(Ps %^ i)get_pst ''pst'') = broken  /\\ st'= stopped)  /\\
       (ALL j:(#1 .. NP). j ~= i -->(Ps' %^ j) = (Ps %^ j)) /\\
       (PROJ(Ps %^ i)get_mst ''mst'') :{closed,opening}   
                         --> (PROJ(Ps' %^ i)get_pst ''pst'') = noflow /\\
       (PROJ(Ps %^ i)get_mst ''mst'') = open 
                         --> (PROJ(Ps' %^ i)get_pst ''pst'' = flow)   /\\
       (PROJ(Ps %^ i)get_mst ''mst'') = broken 
                         --> (PROJ(Ps' %^ i)get_pst ''pst'') = noflow /\\
       (PROJ(Ps' %^ i)get_mst ''mst'') = (PROJ(Ps %^ i)get_mst ''mst'') 
--- 
"

 "+-- PUMP_REPAIRED ---
         %Delta SteamBoiler; 
         %Xi SensorModels;
         %Xi ValveModel;
         i : (#1 .. NP)
|--
         alarm = OFF /\\
         ((PROJ(Ps %^ i)get_mst ''mst'')  = broken  /\\ st' = st) \\/
         (~(PROJ(Ps %^ i)get_mst ''mst'') = broken) /\\ st'=stopped /\\
         (ALL j : (#1 .. NP). j ~= i--> (Ps' %^ j)=(Ps %^ j))    /\\
         (PROJ(Ps' %^ i)get_mst ''mst'') = closed /\\
         ((PROJ(Ps %^i)get_pst ''pst'')=flow /\\
          (PROJ(Ps' %^i)get_pst ''pst'')= broken) \\/
         (get_pst(Ps %^i) ~= flow /\\ 
          get_pst(Ps' %^i) = get_pst(Ps %^ i)) 
---
"
(* In order to show both forms of projections ... *)

"
+-- STEAM_BOILER_WAITING ---
       %Delta SteamBoiler; 
       %Xi SensorModels;
       alarm: Alarm;
       st: PhysModes;
       st': PhysModes
|--
       alarm = OFF /\\
       st = waiting /\\
       WaterAboveNormal --> st' = adjusting /\\ ValveOpen'   /\\ PumpsClosed' /\\
       WaterBelowNormal --> st' = adjusting /\\ ValveClosed' /\\ PumpsOpen'   /\\
       WaterNormal      --> st' = ready     /\\ (%Xi ActorModels)
---
"


"Pumps1 == (PumpsOpen  =+=> %not(PumpsClosed))"
"Water1 == (WaterAboveNormal  =+=> %not(WaterNormal))"  
"Water2 == (WaterBelowNormal  =+=> %not(WaterNormal))"
"Water3 == (WaterAboveNormal  =+=> %not(WaterBelowNormal))"

"Water4 == %not(WaterBelowNormal) /\\ %not(WaterAboveNormal) =+=> WaterNormal"
end
    

