package lexicalanalyzer;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class Syntax {

    static int i = 0;
    static int scope=0;
    static ArrayList<tokenSet> token = new ArrayList<>();
    
    String TM = "";   //for insert and lookup
    String SM="";
    String T = "";
    String N = "";
    String N2 = "";
    String OP = "";
    String OP2 = "";
    String T2="";  
    
    String P="";  //for pList
    String P2="";  //for pList
    int plist=0;
    
    int CN=0;     //flag to check classname
    
    String[] TY;    //class case
    String[] TY2;  //obj case
    String[] TY3; //for Function Table
   
    
    int retCheck=0; //for function return type
    String retValue="";
    int retType=0;
    String fnType="";
    
    String Ltype="";
    String Rtype="";
    String value=""; //for comapatibility
    String resType="";
    
    
    int varfl=0;         //flag varibale to check class level or function level
    
    int upperCheck=0;  //to check upper level of declarations
    int levels=0;
    int curScCheck=0;  //to check current scope
    int mainLevel=0; 
    int valNewScope=0;
            
    int brCheck=0; //for break statement
    
    int consCheck=0; //for constructor
    int thCheck=0; //for this
    int suCheck=0; //for super
    int suOccur=0;
    int thOccur=0;
    String suValue="";
    
    String assignCheck="";
    
    static int pubCheck = 0;  //for main occurence
    
    Semantic sm;
    ClassBodyTable cb;
    ClassBodyTable cb2;
    
    public Syntax(){}

    public Syntax(ArrayList<tokenSet> token1) {

        token = token1;
        sm= new Semantic("","","","","",cb);
       

    }

    public void validate() {

        if (start()) {

            if (i == token.size() - 1) {
                System.out.println("Valid Syntax");
            }

        } else {

            System.out.println("Error Occured At Line No: " + (token.get(i).line + 1));
        }

        sm.showData();
       
    }

    boolean dowhile_st() {

        if (token.get(i).CP.equals("do")) {
                //sem
                brCheck=1;
                //sem
            i++;

            if (body()) {
                //sem
                brCheck=0;
                //sem
                if (While()) {
                    //System.out.println("ch-"+token.get(i).VP);
                    if (token.get(i).CP.equals(";")) {

                        return true;
                    }
                }

            }

        }
        return false;
    }

    boolean break_st() {
        if (token.get(i).CP.equals("break") && token.get(i + 1).CP.equals(";")) {
            
            //sem
            if(brCheck==0){
                System.out.println("Error: break outside switch or loop");
            }
            //sem
            i += 2;
            return true;
        }

        return false;
    }

    boolean case_body2() {

        if (case_body()) {

            return case_body2();

        } else if (token.get(i).CP.equals("}") || token.get(i).CP.equals("default")) {

            // i--;  //creating issue as i++ also in c_body
            return true;
        }

        return false;

    }

    boolean case_body() {
        if (break_st()) {

            if (token.get(i).CP.equals("case") || token.get(i).CP.equals("}") || token.get(i).CP.equals("default")) {

                return case_st();
            }

        }
        if (While()) {

            return true;
        }
        if (dowhile_st()) {

            return true;
        }
        if (for_st()) {

            return true;
        }
        if (if_else()) {

            return true;
        }
        if (token.get(i).VP.equals("this") && token.get(i + 1).VP.equals(".")) {
            i += 2;

            if (token.get(i).CP.equals("ID")) {

                i++;

                if (Z(T)) {

                    return true;
                }

            }

        }
        if (token.get(i).VP.equals("super") && token.get(i + 1).VP.equals(".")) {
            i += 2;

            if (token.get(i).CP.equals("ID")) {
                i++;
                if (Z(T)) {

                    return true;
                }

            }

        }

        if (token.get(i).CP.equals("IncDec")) {
            i++;
            if (token.get(i).CP.equals("ID")) {

                if (Z(T)) {

                    return true;
                }

            }

        }
        if (token.get(i).CP.equals("static")) {
            i++;

            if (SST4()) {
                return true;
            }

        }
        if (token.get(i).CP.equals("DT") || token.get(i).CP.equals("String")) {
            i++;

            if (SST5(T)) {

                return true;
            }

        }

        if (token.get(i).VP.equals("public") || token.get(i).VP.equals("private")) {
            i++;

            if (SST2()) {

                return true;
            }

        }

        if (token.get(i).CP.equals("ID")) {

            i++;
      
               
            if (Z(T)) {
               
                return true;
            } else if (token.get(i).CP.equals("ID")) {

                i++;
                if (init2(T,N)) {
                    i++;
                    return true;
                }
            }

        }

        return false;
    }

    boolean constant(String T,String N,String OP) {
       
        //sem
        if(plist==1){
        for(int j=0;j<token.get(i).CP.length();j++){
         
            if(token.get(i).CP.charAt(j)=='-'){
               P=P+token.get(i).CP.substring(0,j);

               break;
            }
         
        }
        OP="No-check";
        }
        
        if(!fnType.equals("")&& OP.equals("ret")){  //for function return type check
            T=fnType;
           
            
        }
       
       
        //sem
        if (token.get(i).CP.equals("int-const")) {
            
            value=token.get(i).CP;     
           
           
              
            if(!sm.compatibilityCheck(T, value, OP)){
                
               System.out.println("Type Mismatch Error");
            }
            
            i++;

            return true;

        } else if (token.get(i).CP.equals("char-const")) {
            value=token.get(i).CP; 
          
            
            if(!sm.compatibilityCheck(T, value, OP)){
                
               System.out.println("Type Mismatch Error");
            }
            i++;

            return true;
        } else if (token.get(i).CP.equals("String-const")) {
            
    
             value=token.get(i).CP; 
            
            
            if(!sm.compatibilityCheck(T, value, OP)){
                
               System.out.println("Type Mismatch Error");
            }
            
            
            
            i++;

            return true;
        } else if (token.get(i).CP.equals("bool-const")) {
            value=token.get(i).CP;
         
            
            if(!sm.compatibilityCheck(T, value, OP)){
                
               System.out.println("Type Mismatch Error");
            }
            i++;

            return true;
        } else if (token.get(i).CP.equals("float-const")) {
            value=token.get(i).CP; 
          
            
            if(!sm.compatibilityCheck(T, value, OP)){
                
               System.out.println("Type Mismatch Error");
            }

            i++;
             
            return true;
        }
        return false;
    }

    boolean case_st() {

        if (token.get(i).CP.equals("case")) {
            i++;
            if (constant(T,N,OP)) {

                if (token.get(i).CP.equals(":")) {
                    i++;

                    if (case_body2()) {

                        return case_st();

                    }
                }

            }

        } else if (token.get(i).CP.equals("default") && token.get(i + 1).CP.equals(":")) {
            i += 2;

            if (MST()) {
                i++;
                return true;
            }
            return false;
        }
        if (token.get(i).CP.equals("}")) {

            return true;
        }

        return false;
    }

    boolean switch_st() {
        if (token.get(i).CP.equals("switch")) {

            i++;
            if (token.get(i).CP.equals("(")) {

                i++;
                if (OE(T,OP)) {

                    if (token.get(i).CP.equals(")")) {
                        i++;

                        if (token.get(i).CP.equals("{")) {
                            i++;
                            if (case_st()) {

                                if (token.get(i).CP.equals("}")) {
                                    i++;
                                    return true;
                                }
                            }

                        }

                    }

                }
            }

        }

        return false;
    }

    boolean return_st() {

        if (token.get(i).CP.equals("return")) {
            
            //sem
            retCheck=1;
            retType=1;
            if(!fnType.equals("")){
              T=fnType;
              OP="ret";
           
            }
            //sem
            
            
            i++;
          
            if (token.get(i).CP.equals(";")) {
                i++;
                return true;
            } 
            else if (OE(T,OP)) {
                   
                if (token.get(i).CP.equals(";")) {
                    
                    //sem
                      if(!token.get(i+1).CP.equals("}")){   //after return __ ; (necessary that scope will end with } )
                       System.out.println("Unreacheable Statements");
                      }
                    //sem
                    
                    i++;
                      
                    return true;
                }

            } else if (th()) {
                if (ZF(T,OP)) {
                    if (token.get(i).CP.equals(";")) {
                        i++;
                        return true;
                    }

                }

            }

        }
        return false;
    }

    boolean th() {
        if (token.get(i).VP.equals("this") && token.get(i + 1).VP.equals(".")) {
            i += 2;
            return true;

        } else if (token.get(i).VP.equals("super") && token.get(i + 1).VP.equals(".")) {
            i += 2;
            return true;

        }

        return true;
    }

    boolean C1() {

        if (token.get(i).CP.equals(";")) {
            i++;
            return true;
        } else if (token.get(i).CP.equals("DT")) {

            i++;

            if (dec(T,SM)) {
                i++;
                return true;
            }

        } else if (th()) {

            if (token.get(i).CP.equals("ID")) {

                i++;

                if (Z(T)) {

                    return true;
                }
            }

        }

        return false;
    }

    boolean for_Z() {

        if (token.get(i).VP.equals(".")) {
            i++;

            if (token.get(i).CP.equals("ID")) {
                i++;
                return Z(T);    //recursive working
            }

        } else if (X4()) {    //square brackets occurs [][]

            if (Z1()) {
                return true;
            }

        } else if (token.get(i).CP.equals("IncDec")) {
            i++;
            return true;

        } else if (assign_For()) {  //= ocuurs

            return true;
        } else if (token.get(i).CP.equals("(")) {    //function call

            i++;

            if (arguments()) {

                if (token.get(i).CP.equals(")")) {
                    i++;
                    if (Z2(T)) {
                        return true;
                    }
                }
            }

        }

        return false;

    }

    boolean assign_For() {

        if (token.get(i).VP.equals("=")) {
            i++;

            if (OE(T,OP)) {

                return true;
            }

        } else if (token.get(i).CP.equals("Compound Assignment")) {
            i++;
            if (OE(T,OP)) {

                return true;
            }

        }

        return false;
    }

    boolean for_st() {

        if (token.get(i).CP.equals("for")) {
            
            //sem 
            brCheck=1;
            //sem

            i++;
            if (token.get(i).CP.equals("(")) {

                i++;

                if (C1()) {

                    if (token.get(i).CP.equals(";")) { //when ;; occurs

                    } else if (!OE(T,OP)) { //if OE false then it enters

                        return false;
                    }

                    if (token.get(i).CP.equals(";")) {

                        i++;
                        if (token.get(i).CP.equals("IncDec") && token.get(i + 1).CP.equals("ID")) {
                            
                            i += 2;

                        } else if (th()) {

                            if (token.get(i).CP.equals("ID")) {
                                i++;

                                if (!for_Z()) {  //same as above OE
                                    return false;

                                }

                            }

                        }
                    }
                    if (token.get(i).CP.equals(")")) {

                        i++;

                        if (body()) {
                            
                            //sem
                            brCheck=0;
                            //sem
                            return true;
                        }

                    }

                }

            }
        }
        return false;
    }

    boolean oelse() {

        if (token.get(i).CP.equals("else")) {
            
            Semantic.upCh=1;
            
            i++;
            if (body()) {
                
                Semantic.upCh=0;
                
                return true;
            }

        }
        return false;
    }

    boolean if_else() {
           
        
        
        if (token.get(i).CP.equals("if")) {
            
            
            
            i++;

            if (token.get(i).CP.equals("(")) {

                i++;
                if (OE(T,OP)) {

                    if (token.get(i).CP.equals(")")) {
                        
                       
                       
                        i++;
                        if (body()) {
                            
                            
                            
                            if (oelse()) {
                                
                                return true;
                            }
                            return true;
                        }

                    }

                }

            }

        }

        return false;
    }

    boolean inherit() {

        if (token.get(i).CP.equals("extends") && token.get(i + 1).CP.equals("ID")) {
             sm.setExtend(token.get(i+1).VP);
             
             TY=sm.lookUp_MT(token.get(i+1).VP,cb);
            if(TY==null){
                
              System.out.println(token.get(i+1).VP+" class is Undeclared ");
            }
           
             if(TY!=null && TY[0]=="class"&&TY[2]=="fin"){
                System.out.println(token.get(i+1).VP+" class is final it can not be inherit");
             }
             i+=2;
            return true;
        }
       
        sm.setExtend("-");
        return true;
    }

    boolean ZF1(String T, String N) {

       /* if (token.get(i).VP.equals(".") && token.get(i + 1).CP.equals("ID")) {

            i += 2;
            if (ZF1()) {

                return true;
            }

        } */
       
      if(token.get(i).VP.equals(".") && token.get(i+1).CP.equals("ID")){
          
  
           //sem
               N=token.get(i+1).VP;
                if(!token.get(i+2).VP.equals("(")){                          //o.x=5;

                   
                       if (CN==1) {                                 //direct class name case
                           
                        TY = sm.lookUp_att_DT(N, T);
                            
                        if (TY == null) {

                            System.out.println(N + " is Undeclared");
                        }
                        if (TY!=null && !TY[2].equals("static")) {
                            System.out.println("Error: " + N + "  is non static ");
                        }
                        if(TY!=null){
                          T=TY[0];
                        }
                        CN=0;
                    } 
                         else {                                               //object case
                          
                        TY2 = sm.lookUp_att_DT(N, T);
                            
                        if (TY2 == null) {

                            System.out.println(N + " is Undeclared");
                        }
                        if(TY2!=null){
                             T=TY2[0];
                             
                        }

                    }
                    
                   
               }
             
               
                //sem
         
          i+=2;
           
          return ZF1(T,N);
      }
       
       
        else if (token.get(i).CP.equals("(")) {    //function call
            
            
            
              
                
            i++;
            
            if (arguments()) {
                
                //sem
             
                   if (CN == 1) {
                    TY = sm.lookUp_att_FT(N, P, T);
                    if (TY == null) {
                        System.out.println(N + " function is Undecalared");
                    }

                    if (TY != null && !TY[2].equals("static")) {
                        System.out.println("Error: " + N + "  is non static ");
                    }
                    CN=0;
                } else {
                       
                    TY2 = sm.lookUp_att_FT(N, P, T);
                    if (TY2 == null) {
                        System.out.println(N + " function is Undecalared");
                    }
                }
                 P="";
                //sem
                
                 
                if (token.get(i).CP.equals(")")) {
                    
                     //sem
                    if(TY==null && TY2!=null){
                                        
                     T=TY2[0];
                       
                    }
                    else if(TY!=null){
                      T=TY[0];
                    }
                   
                    //sem
                  
                    i++;
                   
                    return ZF1(T,N);
                }
            }
         
        }
            else if (X4()) {
              
               return ZF1(T,N);

        }  
            
        
        else if(token.get(i).CP.equals("Relational Operator")||token.get(i).CP.equals("PM")||
                token.get(i).CP.equals("MDM")||token.get(i).VP.equals("&")||token.get(i).VP.equals("|")){
             
            //sem
                OP=token.get(i).VP;
                Ltype=T;
                resType=T;   
                
            //sem 
                 
                 return true;
            }
        
        
 
        else if (token.get(i).CP.equals(")") || token.get(i).CP.equals("]") || token.get(i).CP.equals(",") || token.get(i).CP.equals(";")) {   //for exit

            if (!token.get(i - 1).CP.equals("(") && !token.get(i - 1).CP.equals("[") && !token.get(i - 1).CP.equals(",")) { //its for that OE not be null
             
                //sem
                
                Rtype=T;
                Rtype=Rtype+"-const";
                 if (!fnType.equals("") && OP.equals("ret")) {  //for function return type check
                          Ltype = fnType;
                           T=fnType;
                          fnType = "";
                          for(int k=0;k<Rtype.length();k++){   
                            if(Rtype.charAt(k)=='-'){
                                Rtype=Rtype.substring(0,k);
                            }
                          } 
                  }
                 else{
                  Ltype=resType;       
                  
                 }
                   
                if (!Rtype.equals("") && !Ltype.equals("")) {
                    if (!sm.compatibilityCheck(Ltype, Rtype, OP)) {
                        System.out.println("Type Mismatch Error");
                    }
                    Ltype = "";
                    Rtype = "";
                }
                //sem
                  
                return true;
            }

        }
          
        return false;
    }

    boolean ZF(String T,String OP) {
        
    
        if (token.get(i).CP.equals("ID")) {
          
           
           //sem
             
             
             TY = sm.lookUp_MT(token.get(i).VP, cb);
                   
                 
                  if(TY!=null){
                      
                    if (token.get(i).VP.equals(TY[3])) {  //calling through Class name
                       
                       CN=1;
                       T=TY[3];
                       
                    }
                  }
                   
           
                  else {                              //calling through object
                      T = sm.lookUp_FT(token.get(i).VP, sm.scope,upperCheck);
                      
                     
                          Ltype = T;
                      
                       
                      if (T == null) {
                          System.out.println(token.get(i).VP + " is Undeclared");
                      }
                  } 
                 
             
           //sem         
            
             i++;
              
            if (ZF1(T,N)) {
                 
                return true;
            }
          
           // return true;
        }
 
        return false;
    }
    
   

    boolean F(String T,String OP) {
          
        //sem
        try{
        if(!Ltype.equals("")){
          T=Ltype;
          
        }
        }
        catch(Exception e){
           System.out.println("Exception"+e);
        }
        //sem
          
        if (constant(T,N,OP)) {
          
            return true;
        } 
        if (ZF(T,OP)) { //ID scenarios
            
            return true;
        } 
        if (token.get(i).VP.equals("this") && token.get(i + 1).VP.equals(".")) {
            i += 2;
            if (ZF(T,OP)) {
                return true;
            }

        } 
        if (token.get(i).VP.equals("super") && token.get(i + 1).VP.equals(".")) {
            i += 2;
            if (ZF(T,OP)) {

                return true;
            }

        } 
        if (token.get(i).VP.equals("!")) {
            i++;
            if (F(T,OP)) {                        //issue

                return true;
            }

        }  
        if (token.get(i).CP.equals("(")) {     // (OE) comes in OE
            i++;
            if (OE(T,OP)) {

                i++;

                if (token.get(i).CP.equals(")")) {
                            i++;
                    return true;
                }

            }

        }
        //if (token.get(i).CP.equals(")")) { //when OE is NULL

         //   return true;
        //}
        
        return false;
    }

    boolean T1(String T,String OP) {
         
        if (token.get(i).CP.equals("MDM")) {
             OP=token.get(i).VP;
          
            i++;
           
            return T(T,OP);

        }
          else if(token.get(i).CP.equals("PM")||token.get(i).CP.equals("Relational Operator")||token.get(i).VP.equals("&")||token.get(i).VP.equals("|")||token.get(i).CP.equals(")")||token.get(i).CP.equals("]")||token.get(i).CP.equals(";")
                    ||token.get(i).CP.equals("}")||token.get(i).CP.equals(",")){
			
			
                       
			
			return true;	
		}

        return false;
    }

    boolean T(String T,String OP) {
      
        if (F(T,OP)) {
        
            if (T1(T,OP)) {
                
                return true;
            }
           
        }

        return false;
    }

    boolean E1(String T,String OP) {

        if (token.get(i).CP.equals("PM")) {
            
            
            OP=token.get(i).VP;
            
            i++;
            return E(T,OP);

        }
          else if(token.get(i).CP.equals("Relational Operator")||token.get(i).VP.equals("&")||token.get(i).VP.equals("|")||token.get(i).CP.equals(")")||token.get(i).CP.equals("]")||token.get(i).CP.equals(";")
                    ||token.get(i).CP.equals("}")||token.get(i).CP.equals(",")){
			
			
			
			return true;	
		}

        return false;
    }

    boolean E(String T,String OP) {

        if (T(T,OP)) {
             
            if (E1(T,OP)) {
                return true;
            }
         
        }

        return false;
    }

    boolean RE1(String T,String OP) {

        if (token.get(i).CP.equals("Relational Operator")) {
             OP=token.get(i).VP;
           
            i++;
           
            return RE(T,OP);
        }
          else if(token.get(i).VP.equals("&")||token.get(i).VP.equals("|")||token.get(i).CP.equals(")")||token.get(i).CP.equals("]")||token.get(i).CP.equals(";")
                    ||token.get(i).CP.equals("}")||token.get(i).CP.equals(",")){
			
			 
			
			return true;	
		}

        return false;
    }
    

    boolean RE(String T,String OP) {
        if (E(T,OP)) {
            if (RE1(T,OP)) {
                return true;
            }
           
        }

        return false;
    }

    boolean AE1(String T,String OP) {

        if (token.get(i).VP.equals("&")) {
            OP="&";
            i++;

            if (RE(T,OP)) {

                if (AE1(T,OP)) {
                    return true;

                }
             
            }

        }
          else if(token.get(i).VP.equals("|")||token.get(i).CP.equals(")")||token.get(i).CP.equals("]")||token.get(i).CP.equals(";")
                    ||token.get(i).CP.equals("}")||token.get(i).CP.equals(",")){
			
			 
			OP=token.get(i).VP;
			return true;	
		}
        

        return false;
    }

    boolean AE(String T,String OP) {

        if (RE(T,OP)) {
            if (AE1(T,OP)) {
               return true;
            }
         
        }

        return false;
    }

    boolean OE1(String T,String OP) {
        if (token.get(i).VP.equals("|")) {
            OP="|";
            i++;

            if (AE(T,OP)) {

                if (OE1(T,OP)) {
                    return true;
                }
              
            }
        }
          else if(token.get(i).CP.equals(")")||token.get(i).CP.equals("]")||token.get(i).CP.equals(";")
                    ||token.get(i).CP.equals("}")||token.get(i).CP.equals(",")){
			
			 
			
			return true;	
		}

        return false;
    }

    boolean OE(String T,String OP) {

        if (AE(T,OP)) {
         
            if (OE1(T,OP)) {
              return true; 
            }
        }

        return false;
    }

    
    
    //For Assignment
     boolean assign_F(String T,String N,String OP){
         
          //sem
          try{
          if(!Ltype.equals("")){
             
             T=Ltype;
              
          }
          }
          catch(Exception e){
          System.out.println(e);
          }
          //sem
       
          
           if (constant(T,N,OP)) {
           
            return true;
         } 
           
          else if(token.get(i).CP.equals("ID")){
             
              //sem
                
                TY = sm.lookUp_MT(token.get(i).VP, cb);
                   
                 
                  if(TY!=null){
                      
                    if (token.get(i).VP.equals(TY[3])) {  //calling through Class name
                       
                       CN=1;
                       T=TY[3];
                    }
                  }
                   
           
                  else {                              //calling through object
                      T = sm.lookUp_FT(token.get(i).VP, sm.scope,upperCheck);
                      
                     // Ltype=T;
                    
                        
                      if (T == null) {
                          System.out.println(token.get(i).VP + " is Undeclared");
                      }
                  } 
              
              
              //sem
             i++;
                 
               if (Z(T)) { //ID scenarios
                    
                   //sem
                    if(Rtype.equals("void")){
                      System.out.println("void can not be converted to "+Ltype);
                    }
                    if(!Rtype.equals("")&&!Ltype.equals("")){
                     Rtype=Rtype+"-const";
                       
                    if(!sm.compatibilityCheck(Ltype, Rtype, OP)){
                        
                      System.out.println("Type Mismatch Error");
                     
                    }
                    Ltype="";
                    Rtype="";
                    }
                    Rtype=T;
                     
                   
                   //sem
                  
                   return true;
                 }
             
                           
             
        } else if (token.get(i).VP.equals("this") && token.get(i + 1).VP.equals(".")&&token.get(i+2).CP.equals("ID")) {
            i += 3;
            if (Z(T)) {
                return true;
            }

        } else if (token.get(i).VP.equals("super") && token.get(i + 1).VP.equals(".")&&token.get(i).CP.equals("ID")) {
            i += 3;
            if (Z(T)) {

                return true;
            }

        } else if (token.get(i).VP.equals("!")) {
            i++;
            if (assign_F(T,N,OP)) {                        //issue

                return true;
            }

        }  else if (token.get(i).CP.equals("(")) {     // (OE) comes in OE
            i++;
            if (assign_OE(T,N,OP)) {

                i++;

                if (token.get(i).CP.equals(")")) {
                            i++;
                    return true;
                }

            }

        }
        //if (token.get(i).CP.equals(")")) { //when OE is NULL

         //   return true;
        //}
            
        return false;
    
    
       
    }
    boolean assign_T1(String T,String N,String OP) {
                 
        if (token.get(i).CP.equals("MDM")) {
            
           OP=token.get(i).VP;
           
            i++;
             if(token.get(i).CP.equals(";")){
                i--;
               return false;
            }
            
            return assign_T(T,N,OP);

        }
          else if(token.get(i).CP.equals("PM")||token.get(i).CP.equals("Relational Operator")||token.get(i).VP.equals("&")||token.get(i).VP.equals("|")||token.get(i).CP.equals(")")||token.get(i).CP.equals("]")||token.get(i).CP.equals(";")
                    ||token.get(i).CP.equals("}")||token.get(i).CP.equals(",")){
			
			  
			
			return true;	
		}

        return false;
    }

    boolean assign_T(String T,String N,String OP) {

        if (assign_F(T,N,OP)) {
           
            if (assign_T1(T,N,OP)) {
                
                return true;
            }
          
        }
    
        return false;
    }

    boolean assign_E1(String T,String N,String OP) {
         
        if (token.get(i).CP.equals("PM")) {
             OP=token.get(i).VP;
             
            i++;
            if(token.get(i).CP.equals(";")){  //a=3+
                i--;
               return false;
            }
            return assign_E(T,N,OP);

        }
         else if(token.get(i).CP.equals("Relational Operator")||token.get(i).VP.equals("&")||token.get(i).VP.equals("|")||token.get(i).CP.equals(")")||token.get(i).CP.equals("]")||token.get(i).CP.equals(";")
                    ||token.get(i).CP.equals("}")||token.get(i).CP.equals(",")){
			
			 
			
			return true;	
		}
     
        return false;
    }

    boolean assign_E(String T,String N,String OP) {

        if (assign_T(T,N,OP)) {
            
            if (assign_E1(T,N,OP)) {
                return true;
            }
           
        }

        return false;
    }

    boolean assign_RE1(String T,String N,String OP) {

        if (token.get(i).CP.equals("Relational Operator")) {
            OP=token.get(i).VP;
            i++;
             if(token.get(i).CP.equals(";")){
                i--;
               return false;
            }
            return assign_RE(T,N,OP);
        }
        else if(token.get(i).VP.equals("&")||token.get(i).VP.equals("|")||token.get(i).CP.equals(")")||token.get(i).CP.equals("]")||token.get(i).CP.equals(";")
                    ||token.get(i).CP.equals("}")||token.get(i).CP.equals(",")){
			
			
			
			return true;	
		}

        return false;
    }

    boolean assign_RE(String T,String N,String OP) {
        if (assign_E(T,N,OP)) {
            if (assign_RE1(T,N,OP)) {
                 
               return true;
            }
          
        }
      
        return false;
    }

    boolean assign_AE1(String T,String N,String OP) {

        if (token.get(i).VP.equals("&")) {
            OP=token.get(i).VP;
            i++;
             if(token.get(i).CP.equals(";")){
                i--;
               return false;
            }

            if (assign_RE(T,N,OP)) {

                if (assign_AE1(T,N,OP)) {
                     
                    return true;

                }
                
            }
        }
         else if(token.get(i).VP.equals("|")||token.get(i).CP.equals(")")||token.get(i).CP.equals("]")||token.get(i).CP.equals(";")
                    ||token.get(i).CP.equals("}")||token.get(i).CP.equals(",")){
			
			
			
			return true;	
		}
              

        

        return false;
    }

    boolean assign_AE(String T,String N,String OP) {
       
        if (assign_RE(T,N,OP)) {
              
            if (assign_AE1(T,N,OP)) {
                 
              return true;
            }
        
        }
         
        return false;
    }

    boolean assign_OE1(String T,String N,String OP) {
        if (token.get(i).VP.equals("|")) {
             OP=token.get(i).VP;
            i++;
             if(token.get(i).CP.equals(";")){
                i--;
               return false;
            }

            if (assign_AE(T,N,OP)) {

                if (assign_OE1(T,N,OP)) {
                    return true;
                }
              
            }
        }
          else if(token.get(i).CP.equals(")")||token.get(i).CP.equals("]")||token.get(i).CP.equals(";")
                    ||token.get(i).CP.equals("}")||token.get(i).CP.equals(",")){
			
			
			
			return true;	
		}
        

        return false;
    }

    boolean assign_OE(String T,String N,String OP) {
       
        if (assign_AE(T,N,OP)) {
            if (assign_OE1(T,N,OP)) {
                
                   return true;
            }
            
        }
       
        return false;
    }
    
    
    
    boolean body() {

        if (token.get(i).CP.equals("{")) {
            
            //sem
            levels++;     //levels maintaining so that when level again becomes 0 we set upperCheck to 0
            upperCheck++; 
            curScCheck++;
            mainLevel=1;
            if(sm.scope<=valNewScope){   //if anywhere we dec the scope so here again we assign the new scope value
                
              sm.scope=valNewScope;
            }
            sm.createScope();
            //sme
           
             
            i++;

            if (MST()) {

                i++;

                if (token.get(i).CP.equals("}")) {
                    //sem
                    levels--;
                    Semantic.ifLevel++;   //this is to check siblings scopes
                    Semantic.upCh=1;      //To check in FT by decrementing siblings scopes
                    
                        
                    if (levels == 0 ) {      //when { } inner levels finish we assign again default values to variables
                        upperCheck = 0;
                        Semantic.upCh=0;
                        Semantic.ifLevel=0;
                        Ltype="";
                        Rtype="";
                        
                        if(mainLevel==1){           //maintain the scope
                          valNewScope=sm.scope;
                          sm.scope-=curScCheck;
                          mainLevel=0;
                        }

                    }

            
                    //sem
                    i++;
                   
                    return true;
                }
            }
            
        } else if (token.get(i).CP.equals(";")) {
            i++;
            return true;

        } else if (SST()) {

            return true;

        }

        return true;
    }

    boolean While() {

        
        if (token.get(i).CP.equals("while")) {
                //sem
                brCheck=1;    //as break only occurs in switch or loop
                
                //sem
                  
            i++;
            if (token.get(i).CP.equals("(")) {
                i++;
            }
            if (OE(T,OP)) { //OE will be define

                if (token.get(i).CP.equals(")")) {
                    i++;

                }
            }
            
            //sem
                
            //sem
           

            if (body()) {
                //sem
                brCheck=0;
                
                //sem
              
                return true;

            }

        }

        return false;
    }

    boolean assign_Opr(String T) {
           
        if (token.get(i).VP.equals("=")) {
              
          
           Ltype=T;          
           OP="=";
           
            i++;
          
            if (assign_OE(T,N,OP)) {
                  
                 //sem
                 try{
                if(!Rtype.equals("")&&!Ltype.equals("")){
                  
                    
                 Rtype=Rtype+"-const";
                  
                if(!sm.compatibilityCheck(T,Rtype,OP)){
                  System.out.println("+Type Mismatch Error");
                }
               
                Rtype="";
                }
                 }
                 catch(Exception e){
                   System.out.println("Exception=>"+e);
                 }
                  
                //sem
                 
                if (token.get(i).CP.equals(";")) {

                    return true;
                }
            }

        } else if (token.get(i).CP.equals("Compound Assignment")) {
               OP=token.get(i).VP;
               Ltype=T;
                
               
                  
            i++;
            
            if (assign_OE(T,N,OP)) {
                   
                //sem
                try{
                if(!Rtype.equals("")&&!Ltype.equals("")){
                  
                 Rtype=Rtype+"-const";
                if(!sm.compatibilityCheck(T,Rtype,OP)){
                  System.out.println("Type Mismatch Error");
                }
               
                Rtype="";
                }
                }
                catch(Exception e){
                    System.out.println("exception==>"+e);
                }
                  
                //sem
                
                if (token.get(i).CP.equals(";")) {

                    return true;
                }
            }

        }

      //  i--;  //this is to avoid  } bracket
       
        return false;
    }

    boolean X4() {
        if (token.get(i).CP.equals("[")) {

            i++;

            if (OE(T,OP)) {

                if (token.get(i).CP.equals("]")) {
                    i++;

                    if (X4()) {

                        if (X4()) {

                            return true;

                        }

                        return true;
                    }

                    return true;
                }

            }

        }
        return false;
    }

    boolean Z1() {
        if (token.get(i).VP.equals(".")) {
            i++;

            if (token.get(i).CP.equals("ID")) {
                i++;
                return Z(T);    //recursive working
            }

        } else if (token.get(i).CP.equals("IncDec")) {
            i++;
            if (token.get(i).CP.equals(";")) {
                i++;

                return true;
            }

        } else if (assign_Opr(T)) {

            i++;

            return true;
        }

        return false;
    }

    boolean arg2() {

        if (token.get(i).CP.equals(",")) {
            
            P=P+","; //sem
            
            i++;
         
            return arguments();

        }
       
        return false;
    }

    boolean arguments() {
        
        //sem
        if(!token.get(i).CP.equals(")")){ 
          plist=1;
        }
        //sem
          
        if (OE(T,OP)) {
             
            if (arg2()) {
                
                return true;
            }
           
        }
       
        if (token.get(i).CP.equals(")")) { //if argument is NULL
          
             plist=0; //sem
            return true;
        }
         
        return false;
    }

    boolean Z2(String T) {
      
        if (token.get(i).VP.equals(".")) {
            
            i++;
         
              
            if (token.get(i).CP.equals("ID")) {         
              
               
                //sem
              if(!token.get(i+1).CP.equals("(")){        //.id().x
                     
               
                      try{
                        if (thCheck == 0) {
                            for (int j = 0; j < T.length(); j++) {  //getting return type of method (removing its parameters)
                                if (T.charAt(j) == '-') {
                                    T = T.substring(0, j);
                                    break;
                                }
                            }
                            //Rtype = T;
                                
                        }
                      }
                      catch(Exception e){
                      System.out.println(e);
                      }
                
                      
                      
                       
                TY=sm.lookUp_att_DT(token.get(i).VP,T);
                
                if(TY!=null){
                  T=TY[0];
                }
                
                
                if(TY==null){
                   
                  System.out.println(token.get(i).VP+" is Undeclared");
                }
               }
            /*  else{                                      //.id().id()
               
              
                TY=sm.lookUp_att_DT(token.get(i).VP,T);
                
                 
                if(TY==null){
                    
                  System.out.println(token.get(i).VP+" is Undeclared");
                }
              
              }*/
                //sem
                
                
                
                i++;
                
                if(token.get(i).CP.equals(";")){
                   
                   return false;
                } 
                 
                return Z(T);    //recursive working
            }

        } else if (X4()) {    //square brackets occurs [][]

            if (Z1()) {
                return true;
            }

        } else if (token.get(i).CP.equals(";")) {
           
         
             
            return true;

        }

        return false;
    }

    boolean Z(String T) {      //covers all scenario func call , inc-dec , Assignment
       
          //sem
          if(thCheck==1){  //if Z occurs in this
           T=sm.getName();
           thCheck=0;
          }
          if(suCheck==1){ //if Z occurs in super
           T=sm.getExtend();
           suCheck=0;
          }
          //sem
        if (token.get(i).VP.equals(".")) {
            i++;
              
            if (token.get(i).CP.equals("ID")) {
                
                //sem
               
                if(!token.get(i+1).VP.equals("(")){                          //o.x=5;

                   
                       if (CN==1) {                                 //direct class name case
                           
                        TY = sm.lookUp_att_DT(token.get(i).VP, T);
                            
                        if (TY == null) {

                            System.out.println(token.get(i).VP + " is Undeclared");
                        }
                        if (TY!=null && !TY[2].equals("static")) {
                            System.out.println("Error: " + token.get(i).VP + "  is non static ");
                        }
                        if(TY!=null){
                          T=TY[0];
                        }
                       // CN=0;
                    } 
                         else {                                               //object case
                           
                         
                        TY2 = sm.lookUp_att_DT(token.get(i).VP, T);
                            
                        if (TY2 == null) {

                            System.out.println(token.get(i).VP + " is Undeclared");
                        }
                        if(TY2!=null){
                             T=TY2[0];
                             Ltype=T;
                        }

                    }
                    
                   
               }
             
               
                //sem
                i++;
               
                if(token.get(i).CP.equals(";")){
                   Rtype=T; //sem
               
                   return true;
                }
                   
                return Z(T);    //recursive working
            }

        } else if (X4()) {    //square brackets occurs [][]

            if (Z1()) {
                return true;
            }

        } else if (token.get(i).CP.equals("IncDec") && token.get(i + 1).CP.equals(";")) {
          
            //sem
                OP=token.get(i).VP;
                if(!sm.compatibilityUnary(T,OP)){
                   System.out.println("Bad Type For Unary operand(Type Mismatch)");
                }
              //sem  
                
               i+=2;
           
            return true;

        } else if (token.get(i).CP.equals("(")) {    //function call
             
       
            //sem
             
                     
            N = token.get(i - 1).VP;

                        
              
            //sem
            
            
            
             
            i++;
             
            if (arguments()) {
               
                //sem
             
                   if (CN == 1) {
                     
                    TY = sm.lookUp_att_FT(N, P, T);
                    if (TY == null) {
                        System.out.println(N + " function is Undecalared");
                    }

                    if (TY != null && !TY[2].equals("static")) {
                        System.out.println("Error: " + N + "  +is non static ");
                    }
                   // CN=0;
                } else {
                      
                       try{
                        for(int k=0;k<T.length();k++){  //A--> to remove -->
                         if(T.charAt(k)=='-'){
                             T=T.substring(0,k);
                         }
                       }
                       }
                       catch(Exception e){
                        System.out.println(e);
                       }
                      
                     
                    TY2 = sm.lookUp_att_FT(N, P, T);
                    if (TY2 == null) {
                        System.out.println(N + " function is Undecalared");
                    }
                }
                 P="";
                //sem
                 
                if (token.get(i).CP.equals(")")) {
                    
                    i++;
                       
                    //sem
                    if(TY==null && TY2!=null){
                                        
                     T=TY2[0];
                        
                        try{
                        for(int k=0;k<T.length();k++){  //A--> to remove -->
                         if(T.charAt(k)=='-'){
                             T=T.substring(0,k);
                         }
                       }
                       }
                       catch(Exception e){
                        System.out.println(e);
                       }
                    
                    }
                    else if(TY!=null){
                      T=TY[0];
                         
                        try {
                            for (int k = 0; k < T.length(); k++) {  //A--> to remove -->
                                if (T.charAt(k) == '-') {
                                    T = T.substring(0, k);
                                }
                            }
                        } catch (Exception e) {
                            System.out.println(e);
                        }

  
                    }
                   
                    //sem
                    
                    if (Z2(T)) {
                        
                      //sem
                      try{
                        if (thCheck == 0) {
                            for (int j = 0; j < T.length(); j++) {  //getting return type of method (removing its parameters)
                                if (T.charAt(j) == '-') {
                                    T = T.substring(0, j);
                                    break;
                                }
                            }
                            Rtype = T;
                                
                        }
                      }
                      catch(Exception e){
                      System.out.println(e);
                      }
                
                      
                      //sem
                       if(token.get(i).CP.equals(";")){   //issue
                          i++;
                       }
                      
                        return true;
                    }
                    else{
                       return false;
                    }
                }
            }

        } else if (token.get(i).CP.equals("Compound Assignment")||token.get(i).VP.equals("=")) {                 //= ocuurs
               
             
                   //sem
                    if(TY==null && TY2!=null){
                                        
                     T=TY2[0];
                     Ltype=T;
                       
                    }
                    else if(TY!=null){
                      T=TY[0];
                      Ltype=T;
                    }
                   
                    //sem
              
              
            if (assign_Opr(T)) {
                    
                if (token.get(i).CP.equals(";")) {
                    i++;
                     
                    return true;
                }
               
            }
        }
        
        else if(token.get(i).CP.equals("MDM")||token.get(i).CP.equals("PM")||token.get(i).CP.equals("Relational Operator")
                ||token.get(i).CP.equals("&")||token.get(i).CP.equals("|")){
               Ltype=T;
               OP2=token.get(i).VP;
               
               return true;
        }
        
      else if (token.get(i).CP.equals(";")) { //for exit
           
               if(!token.get(i-1).CP.equals("MDM")||!token.get(i-1).CP.equals("PM")||!token.get(i-1).CP.equals("Relational Operator")
                ||!token.get(i-1).CP.equals("&")||!token.get(i-1).CP.equals("|")){
              // Rtype=T;//sem
                 
           
              //i++
                
              
                return true;
               }
            }
        

       // i--; //to avoid } bracket
           
        return false;
    }

    boolean SST5(String T) {

        if (dec(T,SM)) {
              
            i++;
          
            return true;

        } else if (arr_1init()) {

            if (token.get(i).CP.equals(";")) {
                i++; //creating issue
                return true;
            }
        }
      
        return false;
    }

    boolean SST4() {
        if (token.get(i).CP.equals("DT")) {
            i++;

            if (SST5(T)) {
                return true;
            }

        } else if (token.get(i).CP.equals("ID")) {
            i++;
            if (token.get(i).CP.equals("ID")) {
                i++;
                if (init2(T,N)) {

                    i++;
                    return true;
                }
            }
        }

        return false;
    }

    boolean SST2() {
        if (token.get(i).CP.equals("static")) {
            i++;
            if (SST4()) {
                return true;
            }

        } else if (SST4()) {
            return true;
        }
        return false;
    }

    boolean SST() {
        
          
       
        if (While()) {

            return true;
        }
        if (dowhile_st()) {

            return true;
        }
        if (switch_st()) {

            return true;
        }
        if (break_st()) {

            return true;
        }
        if (return_st()) {

            return true;
        }
        if (for_st()) {

            return true;
        }
        if (if_else()) {

            return true;
        }
        if (token.get(i).VP.equals("this")) {
           
            if(thOccur==0){  //this and super only occurs method or contructors or in params
              System.out.println("illegal start of the statement");
            }
           
            i++;
            if(token.get(i).CP.equals("(")){           //this(5)
                i++;
                if(arguments()){
                    //sem
                    TY=sm.lookUp_att_FT(sm.getName(),P,sm.getName());
                     
                    if(TY==null){
                       System.out.println(sm.getName()+" constructor is undeclared");
                    }
                    //sem
                   if(token.get(i).CP.equals(")")&&token.get(i+1).CP.equals(";")){
                       i+=2;
                      return true;
                   }
                }
            }
                      
            else if (token.get(i).VP.equals(".")&& token.get(i+1).CP.equals("ID")) {
                
                 //sem
                 thCheck=1;
                 N=token.get(i+1).VP;
                  TY=sm.lookUp_att_DT(N,sm.getName());
                  
                  if(TY==null){
                    System.out.println(N+" is undeclared");
                  }
                 //sem 

                i+=2;
                  
                if (Z(T)) {
                   if(token.get(i).CP.equals(";")){
                    i++;
                   }
                    return true;
                }

            }

        }
           if (token.get(i).VP.equals("super")) {
              
               if(suOccur==0){  //this and super only occurs method or contructors or in params
                System.out.println("illegal start of the statement");
              }
           
            i++;
            if(token.get(i).CP.equals("(")){           //super(5)
                //sem
                 if(!token.get(i-2).CP.equals("{")){  //super() should be the first statement in constructor
                   System.out.println("Error: call to super must be first statement in constructor");
                   
                 }
                //sem
                i++;
                if(arguments()){
                    //sem
                    if (!sm.getExtend().equals("-")) {
                        TY = sm.lookUp_att_FT(sm.getExtend(), P, sm.getExtend());

                        if (TY == null) {
                            System.out.println(sm.getExtend() + " consttructor is undeclared");
                        }
                    }
                    else{
                        System.out.println("Error: No Parent Class Exist");
                    }
                        //sem
                        if (token.get(i).CP.equals(")") && token.get(i + 1).CP.equals(";")) {
                            i += 2;
                            return true;
                        }
                    
                }
            }
                      
            else if (token.get(i).VP.equals(".")&& token.get(i+1).CP.equals("ID")) {
                
                 //sem
                 suCheck=1;
                 N=token.get(i+1).VP;
                  TY=sm.lookUp_att_DT(N,sm.getExtend());
                  
                  if(TY==null){
                    System.out.println(N+" is undeclared");
                  }
                 //sem 

                i+=2;
                  
                if (Z(T)) {
                   if(token.get(i).CP.equals(";")){
                    i++;
                   }
                    return true;
                }

            }

        }
     /*   if (token.get(i).VP.equals("super") && token.get(i + 1).VP.equals(".")) {
            i += 2;

            if (token.get(i).CP.equals("ID")) {
                i++;
                if (Z(T)) {

                    return true;
                }
               

            }

        } */

        if (token.get(i).CP.equals("IncDec")) {
            OP=token.get(i).VP;
            i++;
            if (token.get(i).CP.equals("ID")) {
                
                //sem
                T=sm.lookUp_FT(token.get(i).VP,sm.scope,upperCheck);
                if(T==null){
                System.out.println(token.get(i).VP+" is Undeclared");
                }
                
                if(!sm.compatibilityUnary(T,OP)){
                   System.out.println("Bad Type For Unary operand(Type Mismatch)");
                }
                //sem
                
                 
                  i++;
                if (Z(T)) {
                      if(token.get(i).CP.equals(";")){
                        i++;
                      }
                 
                    return true;
                }

            }

        }
        if (token.get(i).CP.equals("static")) {
            i++;

            if (SST4()) {
                return true;
            }

        }
         if (token.get(i).CP.equals("ID")) {
             
           
             
           //sem
              if(token.get(i+1).CP.equals("ID")){   //obj creation case
                  
               if(!sm.insertClass_FT(token.get(i+1).VP,token.get(i).VP,sm.scope,assignCheck,upperCheck)){
                  System.out.println(token.get(i+1).VP+" is Redeclared");
               }
              }
         
              else{  //ID . case                  //object lookup case or class
                  
                   
                  TY = sm.lookUp_MT(token.get(i).VP, cb);
                   
                 
                  if(TY!=null){
                      
                    if (token.get(i).VP.equals(TY[3])) {  //calling through Class name
                       
                       CN=1;
                       T=TY[3];
                       
                    }
                  }
                   
           
                  else {                              //calling through object
                       
                      
                       
                       
                      T = sm.lookUp_FT(token.get(i).VP, sm.scope,upperCheck);
                     
                       Ltype=T;
                        
                      if (T == null) {
                          System.out.println(token.get(i).VP + " is Undeclared");
                      }
                  } 
                 
              }                                   
              //sem
             
            
           
           
            i++;
           
            if (token.get(i).CP.equals("ID")) {
                
                T=token.get(i-1).VP;
               
                i++;
                
                if (init2(T,N)) {
                
                    i++;
                    return true;
                }
                
            }   
               else if (Z(T)) {  // . occurs
                
                return true;
              }

            

        }
        if (token.get(i).CP.equals("DT") || token.get(i).CP.equals("String")) {
            
            //sem
            T=token.get(i).VP;
             resType=T;
            
             //sem
             
             
               
            i++;
             
            if (SST5(T)) {
                  
                  
                return true;
            }
           
        }

        if (token.get(i).VP.equals("public") || token.get(i).VP.equals("private")) {
            i++;

            if (SST2()) {

                return true;
            }
    
        }

       
    
        return false;
    }

    boolean MST() {
         
        if (SST()) {
            
            

              //sem
              Ltype="";
              Rtype="";
              T="";
              OP="";
              T2="";
              P="";
              CN=0;
              SM="";
              TM="";
              //sem
                 
            return MST();
            //return SST();
        } 
        else if (token.get(i).CP.equals("}")) {
           
            //sem
            if(levels==0){            //to check upperLevel but when level is 0 means no upper level exist
             upperCheck=0;
            }
            //sem
         

            i--;   //creating issue as i++ also in c_body
            return true;
        }

        return false;
    }

    boolean main(String TM,String T) {

        if (token.get(i).CP.equals("main") && token.get(i + 1).CP.equals("(") && token.get(i + 2).CP.equals(")")) {
             N="main";
             T=T+"->"+"void";
             if(!sm.insertClass_DT(N,T,SM,TM,cb)){
              System.out.println(token.get(i).VP+" is Redeclare");
             }
            i += 3;

            if (token.get(i).CP.equals("{")) {
                //sem
                sm.createScope();
                varfl=0;
              
                //sem
                i += 1;

                if (MST()) {
            
                    i++;
                     
                    //sem
                    mainLevel=0;
                    //sem
                    return true;
                }
            }
        }

        return false;
    }

    boolean list() {

        if (token.get(i).CP.equals(";")) {
            
          
            return true;
        } else if (token.get(i).CP.equals(",") && token.get(i + 1).CP.equals("ID")) {

            i += 2;

            if (token.get(i).VP.equals("=")) {
                return init(T,N);
            } else if (token.get(i).CP.equals(",")) {
                return list();
            }

        }

        return false;
    }

    boolean init(String T,String N) {
        
        if (token.get(i).VP.equals("=")) {
            
            //sem
            
            Ltype=T;
            OP="=";
            
            //sem
            
            i++;
           
            if (assign_OE(T,N,OP)) {
               
                if (token.get(i).CP.equals("}")) {
                 
                    i--;  //to avoid } bracket
                }
                if ((token.get(i - 1).CP.equals("int-const") || token.get(i - 1).CP.equals("bool-const") || token.get(i - 1).CP.equals("char-const")
                        || token.get(i - 1).CP.equals("string-const") || token.get(i - 1).CP.equals("char-const"))
                        && token.get(i).VP.equals("=")) {     //to resove this issue int a,b=7=8; 

                    return false;
                }
                if (token.get(i).VP.equals("=")) { //float a; b=x=x; 

                    return init(T,N);

                }

                if (list()) {
                  
                    
                    return true;
                }

            }

        }
      
        return false;
    }

    boolean dec(String T,String SM) {
           
        if (token.get(i).CP.equals("ID")) {
            
            //sem
            
            if(token.get(i+1).VP.equals("=")){ //if initialization has been done
                
               assignCheck="1";
            }
          
            if (varfl==1) {               //class level variable
                
                N = token.get(i).VP;
                if (!sm.insertClass_DT(N, T, SM, TM, cb)) {
                    System.out.println(token.get(i).VP + " is Redeclare");
                }
               varfl=0;
            } else {
                
                
                N = token.get(i).VP;
                    
                if (!sm.insertClass_FT(N, T, sm.scope,assignCheck,upperCheck)) {
                    System.out.println(token.get(i).VP + " is Redeclare");
                }
               
                
            }
            //sem
            i++;
            
            if (init(T,N)) {
                //sem
                 assignCheck="0";
                 //sem
                  
                return true;
            } else if (list()) {
                 
                return true;
            }
        }
  
        return false;
    }

    boolean arr() {

        if (token.get(i).CP.equals("[") && token.get(i + 1).CP.equals("]")) {
            i += 2;
            if (token.get(i).CP.equals("[") && token.get(i + 1).CP.equals("]")) {
                i += 2;
                if (token.get(i).CP.equals("[") && token.get(i + 1).CP.equals("]")) {
                    i += 2;
                    return true;
                }
                return true;
            }
            return true;
        }

        return false;
    }

    boolean param2(String T) {
        if (token.get(i).CP.equals(",")) {

            i++;
          if(token.get(i).CP.equals("ID")||token.get(i).CP.equals("DT")||token.get(i).CP.equals("String")){
              T=T+",";
            if (param(T)) {

                return true;
            }
            }
          
        } else if (token.get(i).CP.equals("ID")) { //DT ID
            //sem
            N=token.get(i).VP;
            if(!sm.insertClass_FT(N, P2, sm.scope,assignCheck,upperCheck)){
              System.out.println(token.get(i).VP+" is Redeclared");
            }

            //sem
            i++;

            if (token.get(i).CP.equals(",")) {
                if (param2(T)) {

                    return true;
                }
            } else if (token.get(i).CP.equals(")")) { //follow

                return true;
            }
        } else if (token.get(i).CP.equals("[") && token.get(i + 1).CP.equals("]")) {  //DT[]

            i += 2;
            
             if(token.get(i).CP.equals("[") && token.get(i + 1).CP.equals("]")){
                i+=2;
                if(token.get(i).CP.equals("[") && token.get(i + 1).CP.equals("]")){
                    if(token.get(i).CP.equals("[") && token.get(i + 1).CP.equals("]")){
                         i+=2;
                 }
            
              }
            
            }
           

           if (token.get(i).CP.equals("ID")) {
                return param2(T);
            } else {
               
                return false;
                //return param2();
            }

        } else if (token.get(i).CP.equals(")")) { //for exit
           
            return true;
        }
        //i--;
        return false;
    }

    boolean param(String T) {
             T2=T;
        if (token.get(i).CP.equals("DT") || token.get(i).CP.equals("String")) {
             
         
            if (token.get(i + 1).CP.equals("ID")) {
                
                //sem
                T = T + token.get(i).VP;
                T2 = T;
                P2=token.get(i).VP;
                //sem

                i++;

                if (param2(T)) {
                    return true;
                }
            }

        } else if (token.get(i).CP.equals("ID") && token.get(i + 1).CP.equals("ID")) {
            
            
            
            i += 2;

            if (param2(T)) {
                return true;
            }

        } 
        else if (token.get(i).CP.equals(")")) { //if param is NULL
           
            return true;
        }
     
        return false;
    }

    boolean fn_body(String T,String TM,String SM){
         
        //sem
        if(consCheck==1){
          
          i--;
          
          suValue=token.get(i).VP;
          
        }
       thOccur=1;
       suOccur=1;
        //sem
          
        if (token.get(i).CP.equals("ID") && token.get(i + 1).CP.equals("(")) {
            
          
             
            //sem
             varfl=0;
             sm.createScope();
             N2=token.get(i).VP;
             T=T+"-->";
             
             //sem

            i += 2;
          
            if (param(T)) {
                 
                
                if (token.get(i).CP.equals(")") && token.get(i + 1).CP.equals("{")) {
                   
                    
                     //sem
                     
                       
                    if(!sm.insertClass_DT(N2,T2,SM,TM, cb)){
                        System.out.println(N2+" is Re-declare");
                       
                    }
                    
                   
                    
                     
                 
                     //sem
                     
                      i += 2;
                          
                    if (MST()) {
                        
                        i++;
                    
                    }

                    if (token.get(i).CP.equals("}")) {
                       //sem
                       
                      if(!fnType.equals("")&& retType==0){
                        System.out.println("Error: Missing Return Statement");
                        retType=0;
                      }
                       
                       upperCheck=0;
                       mainLevel=0;
                       suOccur=0;
                       thOccur=0;
                       suValue="";
                     
                       //sem
                       
                        return true;
                    }

                }
            }

        } else if (token.get(i).CP.equals("(")) {

            i++;
            if (param(T)) {

                if (token.get(i).CP.equals(")") && token.get(i + 1).CP.equals("{")) {
                    i += 2;
                    if (MST()) {
                        i++;

                    }

                    if (token.get(i).CP.equals("}")) {

                        return true;
                    }

                }
            }

        }
     
        return false;
    }

    boolean f_ret_type() {

        T=token.get(i).VP;
        if (token.get(i).CP.equals("ID")) {
            i++;
            if (arr()) {

                return true;
            }

        } else if (token.get(i).CP.equals("DT")) {
         
            i++;
            return true;
        } else if (token.get(i).CP.equals("String")) {
            i++;
            return true;
        } else if (token.get(i).CP.equals("void")) {
            i++;
            return true;
        }

        return false;
    }

    boolean abs_meth() {

        if (f_ret_type()) {
            
             T2=T;   //sem
             
            if (token.get(i).CP.equals("ID") && token.get(i + 1).CP.equals("(")) {
                N=token.get(i).VP;
                sm.createScope();
                
                i += 2;
                
                 T=T+"-->";
                if (param(T)) {

                    if (token.get(i).CP.equals(")") && token.get(i + 1).CP.equals(";")) {
                        
                        //sem
                        if(!sm.insertClass_DT(N,T2,"-",TM,cb)){
                          System.out.println(N+" is Redeclare");
                        }
                        //sem
                        
                        i += 1; //creating issue
                        return true;
                    }
                }

            }

        }

        return false;
    }

    boolean c_body1(String TM,String SM) {

        if (class1()) {

            return true;
        } else if (abs_meth()) {

            return true;
        }

        return false;
    }

    boolean c_body2(String TM,String SM) {

        if (class1()) {

            return true;
        } else if (f_ret_type()) {
            if (fn_body(T,TM,SM)) {

                return true;
            }

        }

        return false;
    }

    boolean c_body3(String T,String SM) {

        if (token.get(i).CP.equals("ID")) {
            
            if (fn_body(T,TM,SM)) {

                return true;

            } else if (dec(T,SM)) {
                return true;
            }

        } else if (arr_1init()) {

            if (token.get(i).CP.equals(";")) {
                return true;
            }
        }

        return false;
    }

    boolean init2(String T,String N) {
           
        if (token.get(i).VP.equals("=") && token.get(i + 1).CP.equals("new") && token.get(i + 2).CP.equals("ID")) {
            //sem
            
            
            if(!sm.insertClass_DT(N,T,SM,TM,cb)){
               System.out.println(N+" is Undeclared");
            }
            
            
            OP="obj";
            value=token.get(i+2).VP;
            N=value;
            
              TY=sm.lookUp_MT(value,cb);
            
            if(TY==null){
               
               System.out.println(token.get(i).VP+" is Undeclared");
            }
            if(TY!=null && TY[0]=="class"&&TY[2]=="abs"){
                System.out.println(value+" is abs class object not possible");
            }
            
            
           
            if(!sm.compatibilityCheck(T, value, OP)){
              System.out.println("Obj=>Type Mismatch Error");
            }
            //sem
            i += 3;

            /* if(Y()){  //will design later
               
             }*/
            if (token.get(i).CP.equals("(")) {

                i++;

                if (!arguments()) {
                    
                    return false;
                }
                if (token.get(i).CP.equals(")") && token.get(i + 1).CP.equals(";")) {
                    
                    //sem
                    
                    if (consCheck == 1 || !P.equals("")) {   //constructor checking
                      
                        TY = sm.lookUp_att_FT(N, P, N);

                        if (TY == null) {
                            System.out.println(N + " is Undeclared");
                        }
                    }
                    consCheck=0;
                    //sem

                    i++;

                    return true;
                }

            }

        }
        return false;
    }

    boolean c_body4(String[] TY,String SM) {
        
        if (token.get(i).CP.equals("ID")) {
            
            
            N=token.get(i).VP;
             
            try{
              T=TY[3];
            }
            catch(Exception e){
            System.out.println(e);
            }
            
               
          /*  if(!sm.insertClass_DT(token.get(i).VP,TY[3],SM,TM,cb)){
                System.out.println(token.get(i).VP+" is Redeclare");
            }*/
            
            
            
            i++;
         
          
            if (token.get(i).CP.equals("(")) {
                   i--;                        //this is because fn_body start with ID 
                if (fn_body(T, TM, SM)) {
                   
                    return true;
                }
            }
             else if (init2(T,N)) {

                return true;
            }
              


        } else if (arr()) {

            if (fn_body(T,TM,SM)) {
                return true;
            }

        } else if (fn_body(T,TM,SM)) {
          
            return true;
        }
   
        return false;
    }

    boolean c_body9(String SM) {

        if (token.get(i).CP.equals("abs")) {
            TM="abs";
            i++;
            if (c_body1(TM,SM)) {

                return true;
            }
        } else if (token.get(i).CP.equals("fin")) {
               TM="fin";
            i++;
            if (c_body2(TM,SM)) {
                return true;
            }

        } else if (token.get(i).CP.equals("ID")) {
            
            //sem
            if(token.get(i+1).CP.equals("ID")){  //function
               fnType=token.get(i).VP;
            }
            TY=sm.lookUp_MT(token.get(i).VP,cb);
            //sem
            i++;
           
            
            if (c_body4(TY,SM)) {
                return true;
            }

        } else if (token.get(i).CP.equals("DT") || token.get(i).CP.equals("String")) {
            
            T=token.get(i).VP; //sem
            
            i++;
            
            
            if (c_body3(T,SM)) {
                return true;
            }

        } else if (token.get(i).CP.equals("void")) {
            //sem
            T="void";
            retValue=T;
            //sem
              i++;

            if (pubCheck == 1) {

                if (main(TM,T)) {
                     
                    pubCheck = 2;
                    return true;
                }
                
            }

            if (fn_body(T,TM,SM)) {
                //sem
                if (retValue.equals("void") && retCheck == 1) {
                    System.out.println("Incompatible Types: Unexpected Return Value");
                }
                retValue = "";
                retCheck = 0;
                //sem
                return true;
            }

        } else if (token.get(i).CP.equals("class")) {

            if (class1()) {
                return true;
            }

        }

        return false;
    }

    boolean c_body10() {
        if (token.get(i).CP.equals("abs")) {
            TM="abs";
            i++;
            if (c_body1(TM,SM)) {

                return true;
            }
        } else if (token.get(i).CP.equals("fin")) {
            TM="fin";
            i++;
            if (c_body2(TM,SM)) {
                return true;
            }

        } else if (token.get(i).CP.equals("ID")) {
             TY=sm.lookUp_MT(token.get(i).VP,cb);
            i++;
      
            if (c_body4(TY,SM)) {
                return true;
            }

        } else if (token.get(i).CP.equals("DT") || token.get(i).CP.equals("String")) {
            //sem
            T=token.get(i).VP;
            //sem
            
            i++;
            if (c_body3(T,SM)) {
                return true;
            } else if (arr_1init()) {

                return true;
            }

        } else if (token.get(i).CP.equals("void")) {
            
            //sem
            T="void";
            retValue=T;
            //sem
            
            i++;
              
            if (fn_body(T,TM,SM)) {
                
                //sem
                if (retValue.equals("void") && retCheck == 1) {
                    System.out.println("Incompatible Types: Unexpected Return Value");
                }
                retValue = "";
                retCheck = 0;
                //sem
                
                
                return true;
            }

        } else if (token.get(i).CP.equals("class")) {

            if (class1()) {
                return true;
            }

        } else if (enum_def()) {

            return true;

        }

        return false;
    }

    boolean e_body1() {

        if (token.get(i).CP.equals(",") && token.get(i + 1).CP.equals("ID")) {
            i += 2;
            return e_body1();
        }
        if (token.get(i).CP.equals("}") && token.get(i + 1).CP.equals(";")) {

            return true;
        }

        return false;
    }

    boolean enum_body() {

        if (token.get(i).CP.equals("ID")) {

            i++;

            if (e_body1()) {
                return true;
            }

        }

        if (token.get(i).CP.equals("}") && token.get(i + 1).CP.equals(";")) {

            return true;
        }

        return false;
    }

    boolean enum_def() {

        if (token.get(i).CP.equals("enum") && token.get(i + 1).CP.equals("ID") && token.get(i + 2).CP.equals("{")) {
            
            N=token.get(i + 1).VP;
            T="enum";
            
            
            i += 3;

            if (!enum_body()) {
                return false;
            }

            if (token.get(i).CP.equals("}") && token.get(i + 1).CP.equals(";")) {

                i += 2;
                if (token.get(i).CP.equals("$")) {    //No further checking
                    i--;                            //creating issue
                    return true;
                }

                return c_body();  //c_body again check
            }

        }
        return false;
    }

    boolean c_body() {
          
         //sem
         varfl=1;
         //sem
         
        if (token.get(i).VP.equals("private")) {
            i++;

            if (token.get(i).VP.equals("static")) {
                 SM="static"; //sem
                i++;
                if (c_body9(SM)) {

                    return true;
                }

            } else if (c_body10()) {

                return true;
            }

        }

        if (token.get(i).VP.equals("public")) {

            i++;

            if (token.get(i).VP.equals("static")) {
                   SM="static"; //sem
                if (token.get(i + 1).CP.equals("void") && token.get(i + 2).CP.equals("main")) {

                    pubCheck ++;  //this is to add main
                }
                i++;

                if (c_body9(SM)) {

                    return true;
                }

            } else if (c_body10()) {

                return true;
            }

        }
        if (token.get(i).CP.equals("static")) {
              SM="static";
              varfl=1;
            i++;

            if (c_body9(SM)) {
               
                return true;
            }

        }
        if (enum_def()) {

            return true;
        }

        if (token.get(i).CP.equals("abs")) {
           TM="abs";
            i++;
            if (c_body1(TM,SM)) {

                return true;
            }
        }
        if (token.get(i).CP.equals("fin")) {
            TM="fin";
            i++;
            if (c_body2(TM,SM)) {
                return true;
            }

        }
        if (token.get(i).CP.equals("ID")) {
            
              
            //sem
            if(token.get(i+1).CP.equals("ID")){  //function
               fnType=token.get(i).VP;
            }
             
            TY=sm.lookUp_MT(token.get(i).VP,cb);
            
             try{
                 
                 if(token.get(i+1).CP.equals("(")){  //constructor case    
                     consCheck=1;
                    if(!TY[3].equals(sm.getName())){                //getname have cuurect class name
                             consCheck=1;
                            System.out.println("Invalid Method Declaration");
                       }
                 }
          
            if(TY==null){
            
              System.out.println(token.get(i).VP+" is Undeclared ");
            }
            }
            catch(NullPointerException e) {
	           System.out.println("NullPointerException thrown!");
                 
                   
		}
            
          //sem
           
            i++;
           
            if (c_body4(TY,SM)) {
               
                return true;
            }

        }
        if (token.get(i).CP.equals("DT") || token.get(i).CP.equals("String")) {
            
            //sem
            varfl=1;
            T=token.get(i).VP;
            fnType=T;
            //sem
       
            i++;
            
            if (c_body3(T,SM)) {
                return true;
            }

        }

        if (token.get(i).CP.equals("void")) {
            
            //sem
               T="void";
               retValue="void";
              
            //sem
               
              i++;

            if (fn_body(T,TM,SM)) {
                
                //sem
                if (retValue.equals("void") && retCheck == 1) {
                    System.out.println("Incompatible Types: Unexpected Return Value");
                }
                retValue = "";
                retCheck = 0;
                //sem
                return true;
            }

        }
        if (token.get(i).CP.equals("class")) {

            if (class1()) {
                return true;
            }

        }

        if (token.get(i).CP.equals("}")) { //just to exit
            i--;   //creating issue
            return true;
        }

        return false;
    }

    boolean recu_cbody() { //recursive working
        
      
       
        if (c_body()) {
            
            i++;
            
            //sem
            T="";
            N="";
            SM="";
            TM="";
            T2="";
            OP="";
            OP2="";
            Ltype="";
            Rtype="";
            upperCheck=0;
            P="";
            consCheck=0;
            curScCheck=0;
            fnType="";
            retType=0;
            retValue="";
            retCheck=0;
            suOccur = 0;
            thOccur = 0;
            suValue = "";
            //sem
           
            if (token.get(i).CP.equals("}")) {
                  
                
                return true;
            } else {
                 
                  
                return recu_cbody();

            }
        }
        return false;
    }

    boolean class1() {

        if (token.get(i).CP.equals("class") && token.get(i + 1).CP.equals("ID")) {
             
            
             sm.setType("class");
             sm.setName(token.get(i+1).VP);
             
             
              i += 2;
              
           
            
            if (inherit()) {
                 
               
                  this.cb=new ClassBodyTable();    //createScope()
                  cb.classbody=new ArrayList();  
                  
                  
                
              
                if(!sm.insertClass_MT(sm.name, sm.type, sm.staticModifier,  sm.category, sm.parent,cb)){
                     
                    
                     System.out.println(token.get(i-1).VP+" class is Re-declare");
                  
                 }
                 sm.category="-";
                 
                if (token.get(i).CP.equals("{")) {
                     sm.createScope();
                    i++; //here class body will come

                    /*  if(c_body()){
                     i++;
                      
                     System.out.println(token.get(i).CP+"i=>"+i);
                       if(token.get(i).CP.equals("}")){
                         
                             return true;
                      }

                   } */
                    return recu_cbody();

                }

            }

        }

        return false;

    }

    boolean def3() {
        if (token.get(i).VP.equals("fin")) {
              sm.category="fin";
            i++;
            if (class1()) {

                return true;
            }
        } else if (token.get(i).VP.equals("abs")) {
            sm.category="abs";
            i++;
            if (class1()) {

                return true;
            }

        } else if (class1()) {

            return true;
        }

        return false;

    }

    boolean def2() {

        /*if (token.get(i).CP.equals("static")) {
            i++;
            if (def3()) {

                return true;
            }
        } */
        if (enum_def()) {
            
            return true;
        } else if (def3()) {

            return true;
        }

        return false;
    }

    boolean def1() {

        if (token.get(i).VP.equals("private")) {
            i++;
            if (def2()) {

                return true;
            }

        } else if (token.get(i).VP.equals("public")) {
            i++;
            if (def2()) {

                return true;
            }

        } else if (def2()) {
            return true;

        }

        return false;
    }

    boolean start() {

        if (def1()) {
            i++;
            if (token.get(i).CP.equals("$")) {
                return true;
            } else {

                return start();
            }
        }

        return false;
    }

    boolean arr_start() {
        if (token.get(i).CP.equals("DT")) {
            i++;
            return true;

        }

        return false;
    }

    boolean arr3D() {

        if (token.get(i).CP.equals("new")) {
       
            i++;
            if (arr_start()) {

                if (token.get(i).CP.equals("[")) {
                    i++;
                    //Now OE will check
                    if (OE(T,OP)) {

                        if (token.get(i).CP.equals("]")) {
                            i++;

                        }
                    }

                }
                if (token.get(i).CP.equals("[")) {
                    i++;
                    //Now OE will check
                    if (OE(T,OP)) {

                        if (token.get(i).CP.equals("]")) {
                            i++;

                        }
                    }

                }
                if (token.get(i).CP.equals("[")) {
                    i++;
                    //Now OE will check
                    if (OE(T,OP)) {

                        if (token.get(i).CP.equals("]")) {
                            i++;
                            return true;
                        }
                    }

                }

            }

        }

        return false;
    }

    boolean arr2D() {

        if (token.get(i).CP.equals("new")) {
           
            i++;
            if (arr_start()) {

                if (token.get(i).CP.equals("[")) {
                    i++;
                    //Now OE will check
                    if (OE(T,OP)) {

                        if (token.get(i).CP.equals("]")) {
                            i++;

                        }
                    }

                }
                if (token.get(i).CP.equals("[")) {
                    i++;
                    //Now OE will check
                    if (OE(T,OP)) {

                        if (token.get(i).CP.equals("]")) {
                            i++;
                            return true;
                        }
                    }

                }

            }

        }

        return false;
    }

    boolean arr1D() {

        if (token.get(i).CP.equals("new")) {

            i++;
            if (arr_start()) {

                if (token.get(i).CP.equals("[")) {
                    i++;
                    //Now OE will check
                    if (OE(T,OP)) {

                        if (token.get(i).CP.equals("]")) {
                            i++;

                            return true;
                        }
                    }

                }

            }

        }

        return false;
    }

    boolean arr_3init() {
        if (token.get(i).CP.equals("[") && token.get(i + 1).CP.equals("]")) {
            i += 2;
            if (token.get(i).CP.equals("ID") && token.get(i + 1).VP.equals("=")) {
                i += 2;
                if (arr3D()) {
                    return true;
                }

            }

        } else if (token.get(i).CP.equals("ID") && token.get(i + 1).VP.equals("=")) {
            i += 2;
            if (arr2D()) {
                return true;
            }

        }

        return false;
    }

    boolean arr_2init() {
        if (token.get(i).CP.equals("[") && token.get(i + 1).CP.equals("]")) {
            i += 2;
            if (arr_3init()) {
                return true;
            }
        } else if (token.get(i).CP.equals("ID") && token.get(i + 1).VP.equals("=")) {
            i += 2;
            if (arr1D()) {
                return true;
            }

        }

        return false;
    }

    boolean arr_1init() {
        if (token.get(i).CP.equals("[") && token.get(i + 1).CP.equals("]")) {
            i += 2;
            if (arr_2init()) {
                return true;
            }
        }

        return false;
    }

    public boolean arr_dec() {

        if (arr_start()) {
            if (token.get(i).CP.equals("[") && token.get(i + 1).CP.equals("]") && token.get(i + 2).CP.equals("ID")) {
                i += 3;
                if (arr_1init()) {

                    if (token.get(i).CP.equals(";")) {
                        i++;
                        return true;
                    }

                }

            }

        }

        return false;

    }

}
