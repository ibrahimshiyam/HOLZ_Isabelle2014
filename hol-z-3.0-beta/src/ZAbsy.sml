(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * ZAbsy.sml --- Abstract Syntax for ZETA-Z, Converter, Loader     
 * This file is part of HOL-Z.
 *
 * Copyright (c) 2000-2003 University Freiburg, Germany
 *               2003-2007 ETH Zurich, Switzerland
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
(* $Id: ZAbsy.sml 6729 2007-08-03 05:25:17Z brucker $ *)

(* structure ZAbsy : ZABSY = *)
structure ZAbsy =
    struct 
	
        open ZPrelude HOLogic;
	    
	datatype QuantorKind = Exists | Exists1 | Forall | Let | Set | Lambda
		             | Mu;
	datatype FactKind    = True | False;
        datatype UnaryKind   = Power | Theta | Not | Delta | Xi | Pre 
			     | Hide | Decorate;
	datatype BinaryKind  = And | Or | Iff | Implies | Apply | Compose
	                     | Pipe | Project;
	datatype Branch      = Constant   of string 
	                     | Function   of string * Expr
        and      Expr        = Number     of string
	                     | Denotation of string
			     | NameAppl   of string * Expr list (* variables *)
			     | Tuple      of Expr list 
			     | Product    of Expr list
			     | Binding    of Expr list
			     | Signature  of (string * Expr) list
			     | Display    of Expr list
			     | Cond       of Expr * Expr * Expr
			     | Quantor    of QuantorKind * Expr list * 
                                             Expr list * Expr 
			     | SchemaText of Expr list * Expr list 
			     | Select     of Expr * Expr * Expr
			     | Unary      of UnaryKind * Expr 
			     | Binary     of BinaryKind * Expr * Expr
			     | GivenType  of string 
			     | FreeType   of string * Branch list
			     | Test       of Expr * Expr 
			     | Fact       of FactKind 
			     | Eqn        of string * Expr * Expr
			     | Direct     of string list * Expr 
			     | Gen        of string list * Expr
			     | Type       of Expr 
			     | EmbeddedText of string
			     | ZedFixity of string
			     | Renaming of Expr * (Expr * string) list 
			     | SchemaName of string * Expr * Expr list

	type Item    = Expr
(*	type Item    = Expr * Expr *)
	    
	datatype Section     = ZSection   of string * string list * Item list 

end
