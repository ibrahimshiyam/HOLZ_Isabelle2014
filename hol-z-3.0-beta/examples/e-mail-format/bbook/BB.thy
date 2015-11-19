(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * BB.thy ---
 * This file is part of HOL-Z.
 *
 * Copyright (c) 1998-1999 University Bremen, Germany
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
(* $Id: BB.thy 6739 2007-08-03 06:16:18Z brucker $ *)

BB = Z +  
  
schemas  

[Name, Date]

Report ::= ok | allready_known | not_known 


"+-- BirthdayBook --- 
        birthday : (Name -|-> Date); 
        known    : %P Name 
 |-- 
        known = dom(birthday)

 ---
"
     
"+-- BirthdayBook1 --- 
        dates    : (%N -|-> Date); 
        hwm      : %N;
        names    : (%N -|-> Name) 
 |-- 
        ALL i j. i:($#1..hwm) & j:($#1..hwm) 
                     --> (i~=j --> (names %^ i) ~= (names %^ j)) 
 ---
"  
 
"+-- AddBirthday  --- 
        date?    : Date; 
        name?    : Name;
        %Delta BirthdayBook 
 |--  
        name? ~: known /\\
        birthday'= birthday Un {(name?,date?)}
 ---
"
 
"+-- FindBirthday --- 
        date!   : Date;
        BirthdayBook;
        name?   : Name
 |-- 
        name? : known /\\
        date! = (birthday %^ name?)
 ---
" 

"+-- Remind ---  
        cards!  : %P Name;
        today?  : Date; 
        %Xi BirthdayBook
 |-- 
       cards! = {n. n:known /\\ 
                     (birthday %^ n)= today?}
 ---
"

"+-- Success --- 
        result! : Report
 |--
        result! = ok
 ---"


"+-- AllReadyKnown ---
        name?   : Name;
        result? : Report; 
        %Xi BirthdayBook
 |--
        name? : known /\\ 
        result? = allready_known
 ---
"

"RAddBirthday == (AddBirthday /\\ Success \\/ AllReadyKnown)" 


"+-- InitBirthdayBook ---
        BirthdayBook
 |--
        birthday = {}        
 ---
"

"+-- Abs ---
        BirthdayBook;
        BirthdayBook1
 |--
        known =  {n. ? i : #1..hwm . n = (names %^ i)} /\\
        (! i : #1..hwm. (birthday %^ (names %^ i)) = (dates %^ i) )   
 ---
"

"+-- AddBirthday1 ---
        %Delta BirthdayBook1;
        name? : Name;
        date? : Date
 |--
        (! i : #1..hwm. name? ~= (names %^ i)) /\\

       hwm'   = hwm + #1 /\\
       names' = (names (+) {(hwm', name?)}) /\\
       dates' = (dates (+) {(hwm', date?)})        
 ---
"



"+..
   A : (%N -|-> %P(%Z));
   B : (%Z ---> Report)
 |--
   ! x. (A %^ x) = {} /\\ (B %^ x) = ok
 -.. "  (* Just a test for axiomatic definitions *)


end
