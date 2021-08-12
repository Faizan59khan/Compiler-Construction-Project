package lexicalanalyzer;

import java.util.ArrayList;
import java.util.Stack;



class ClassBodyTable{

  public String name;
  public String type;
  public String staticModifier;
  public String TypeModifier;
  Semantic Link;
    
  ArrayList<ClassBodyTable> classbody;  //we will inialize this when any main table entry occurs
  
  ClassBodyTable CB;
  
  ClassBodyTable(){}
   
  ClassBodyTable( String name, String type,String staticModifier, String TypeModifier){
  
        this.name=name;
        this.type=type;
        this.staticModifier=staticModifier;
        this.TypeModifier=TypeModifier;
  
  }
  
      void showData(){
        for (int i = 0; i < classbody.size(); i++) {
            
            System.out.println("DT=>"+classbody.get(i).name+" "+classbody.get(i).type+" "+classbody.get(i).staticModifier+" "+classbody.get(i).TypeModifier);
        }
      
    } 
  

}




public class Semantic { 
    
    public String name;
    public String type;
    public String staticModifier;
    public String category;
    public String parent;
    public String TypeModifier;
    public String assigned;        //will work later
    ClassBodyTable Link;
    
    
    
   
    
    
    public int scope;
   
    public static int upCh=0;
    public static int ifLevel=0;
    
   
    
    ArrayList<Semantic> clas=new ArrayList();
    ArrayList<Semantic> func=new ArrayList();
   
  
  
     
    

    
    Semantic CN;
    ClassBodyTable CB;
  
  
    public Semantic(){}
    
    
    public Semantic(String name, String type, String staticModifier, String category, String extend,ClassBodyTable Link){
        this.name=name;
        this.type=type;
        this.staticModifier=staticModifier;
        this.category=category;
        this.parent=extend;
        this.Link=Link;
       
    }
    Semantic( String name, String type,String AccModifier, String TypeModifier){
  
        this.name=name;
        this.type=type;
        this.staticModifier=AccModifier;
        this.TypeModifier=TypeModifier;
  
  }
    public Semantic(String name, String type,int scope,String assigned){
  
        this.name=name;
        this.type=type;
        this.scope=scope;
        this.assigned=assigned;
  }
    
  
    

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }

    public String getType() {
        return type;
    }

    public void setType(String type) {
        this.type = type;
    }

    public String getAccModifier() {
        return staticModifier;
    }

    public void setAccModifier(String AccModifier) {
        this.staticModifier = AccModifier;
    }

   

    public String getCategory() {
        return category;
    }

    public void setCategory(String category) {
        this.category = category;
    }

    public String getExtend() {
        return parent;
    }

    public void setExtend(String extend) {
        this.parent = extend;
    }
    
    public ClassBodyTable getLink() {
        return Link;
    }

    public void setLink(ClassBodyTable link) {
        this.Link = Link;
    }
    
    

  
    
    
    public void createScope(){  //whenever new scope or { bracket occurs
        scope++;
        
    }
    
   
    
    
     public boolean insertClass_MT(String name,String type,String staticModifier,String category,String extend,ClassBodyTable Link){
         
     
        this.CN=new Semantic( name, type, staticModifier, category, extend,Link);
        
        
        
        for(int j=0;j<clas.size();j++){           //checking it is not already declared
               if(clas.get(j).name.equals(name)){
                  return false;
               }
             }
        clas.add(CN);
        return true;
        
    }
     
    public boolean insertClass_DT(String name,String type,String staticModifier,String TypeModifier,ClassBodyTable link){
    
           
           
           
         
       link.CB=new ClassBodyTable( name, type, staticModifier,TypeModifier);
          System.out.println("link1=>"+link);
          
         
            
        
       for(int j=0;j<link.classbody.size();j++){                                       //checking that it is not already declared
               if(link.classbody.get(j).name.equals(name)&& link.classbody.get(j).type.equals(type)){ 
                    return false;
               }
             }
         link.classbody.add(link.CB);
         return true;
    }
    
     public boolean insertClass_FT(String name,String type,int scope,String assigned,int upperCheck){
        this.CN=new Semantic(name, type, scope,assigned);
        int elseCh=0;
    
       for(int j=0;j<func.size();j++){                                           //checking that it is not already declared
             
               if(func.get(j).name.equals(name) && func.get(j).scope==scope){          //current scope checking
                    
                 
                    return false;
               }
             }
              
            while (upperCheck != 0) {                          //if something is decalre in its upper scopes
                
              //System.out.println("s"+Semantic.upCh+"s "+scope+"n "+name+" l"+ifLevel);
              
                if(upCh==1){
               scope-=ifLevel+1;
               upperCheck-=ifLevel+1;
                 elseCh=1;
                }
                else{
                scope--;
                upperCheck--;
                }
                upCh=0;
               
             for (int k = 0; k < func.size(); k++) {
                 if (func.get(k).name.equals(name) && func.get(k).scope == scope) {
                    if(elseCh==1){
                     upCh=1;
                    }
                     return false;
                     
                 }
             }
         }
            
            if(elseCh==1){
                     upCh=1;
                    }
         
       func.add(CN);
       return true;
    }
      
    public String[] lookUp_MT(String name,ClassBodyTable link){
        
           String[] arr=new String[4];
          for(int j=0;j<clas.size();j++){                          //checking class exist or not
               if(clas.get(j).name.equals(name)){
                
                   arr[0]=clas.get(j).type;
                   arr[1]=clas.get(j).parent;
                   arr[2]=clas.get(j).category;
                   arr[3]=clas.get(j).name;
                    return arr;
               }
             }
          
         return null;
    }
    
     public String[] lookUp_att_DT(String name,String classType){ //logic=> it comes out with class of that object with that first we find class in MT.
                                                                     //then aproach to its DT link then find entry.
         
                                                                     
         ClassBodyTable link=clas.get(0).Link; 
         int ch=0;
         
         String[] arr=new String[3];
         
          for(int j=0;j<clas.size();j++){                  
               if(clas.get(j).name.equals(classType)){
                   link= clas.get(j).Link;
                   ch=1;
               }
                  
               }
              
              if(ch==1){
           for(int j=0;j<link.classbody.size();j++){                                      
               if(link.classbody.get(j).name.equals(name)){ 
                   
                   arr[0]=link.classbody.get(j).type;
                   arr[1]=link.classbody.get(j).TypeModifier;
                   arr[2]=link.classbody.get(j).staticModifier;
                   
                   return arr;
                   
                   
                    
               }
             }
              }
          
          
        
        
    
          return null;
    }
     public String[] lookUp_att_FT(String name,String argListType,String classType){
        ClassBodyTable link=clas.get(0).Link;    
        String T="";
        int ch=0;     //so it will not consider default link value at any point
        
         String[] arr=new String[3];
         
          for(int j=0;j<clas.size();j++){                  
               if(clas.get(j).name.equals(classType)){
                   link= clas.get(j).Link;
                   ch=1;
               }
                  
               }  
          
              if(ch==1){
           for(int j=0;j<link.classbody.size();j++){                                      
               if(link.classbody.get(j).name.equals(name)){ 
                   
                 
                   for(int k=0;k<link.classbody.get(j).type.length();k++){
                     
                       if(link.classbody.get(j).type.charAt(k)=='>'){
                         T=link.classbody.get(j).type.substring(k+1,link.classbody.get(j).type.length());
                         
                         if(T.equals(argListType)){          //matching param and argumen type
                             arr[0] = link.classbody.get(j).type;
                             arr[1] = link.classbody.get(j).TypeModifier;
                             arr[2] = link.classbody.get(j).staticModifier;

                             return arr;
                           }
                         
                       }
                   
                   }
                   
                    
               }
             }
              }
          
           
          
        
        
    
          return null;
    }
     
    public String lookUp_FT(String name,int scope,int upperCheck){
         int elseCh=0;
         
        
        
        for(int j=0;j<func.size();j++){
           if(func.get(j).name.equals(name) && func.get(j).scope==scope){
               
              return func.get(j).type;
           }
        
        }
        
     
          
        while (upperCheck != 0) {                          //if something is decalre in its upper scopes

            //System.out.println("s"+Semantic.upCh+"s "+scope+"n "+name+" l"+ifLevel);
            if (upCh == 1) {
                scope -= ifLevel + 1;
                upperCheck -= ifLevel + 1;
                elseCh = 1;
            } else {
                scope--;
                upperCheck--;
            }
            upCh = 0;

            for (int k = 0; k < func.size(); k++) {
                if (func.get(k).name.equals(name) && func.get(k).scope == scope) {
                    if (elseCh == 1) {
                        upCh = 1;
                    }
                    return func.get(k).type;

                }
            }
        }
        if (elseCh == 1) {
            upCh = 1;
        }
        
    
          return null;
    }
     
    public boolean compatibilityUnary(String type,String op){
        
        if (op.equals("++") || op.equals("--")) {
            if (type.equals("int") || type.equals("char") || type.equals("float")) {
                return true;
            }
        }
    
        return false;
    }
    
    public boolean compatibilityCheck(String leftType,String rightType,String operator){
        
       
        
        if (operator.equals("obj")) {   //child ref with parent obj checking

            for (int j = 0; j < clas.size(); j++) {
                if (clas.get(j).name.equals(leftType)) {
                    if (clas.get(j).parent.equals(rightType)) {
                        return false;
                    }

                }

            }
           return true;
        }
        
        else if(operator.equals("+")&&leftType.equals("String") && rightType.equals("String-const")){  //string concatenate case
        
           return true;
        }
        
        else if(operator.equals("-")||operator.equals("*")||operator.equals("/")||operator.equals("%")||operator.equals("+")){
            
            if(leftType.equals("int") && rightType.equals("int-const")){
                return true;
           }
         
            else if(leftType.equals("char") &&rightType.equals("char-const")){
                return true;
           }
          
           
        }
        
        
        else if(operator.equals("ret")){
            if(leftType.equals(rightType)){         //when function is of class type
               return true;
            }
              else if(leftType.equals("int") && rightType.equals("int-const")){
                return true;
            }
            else if(leftType.equals("float") &&rightType.equals("float-const")){
                return true;
           }
           
         
           else if(leftType.equals("float") &&rightType.equals("int-const")){
                return true;
           }
            else if(leftType.equals("char") &&rightType.equals("char-const")){
                return true;
           }
         else if(leftType.equals("String") &&rightType.equals("String-const")){
                return true;
           }
            else if(leftType.equals("bool") &&rightType.equals("bool-const")){
                return true;
           }
        }
        
       
        else if(operator.equals("=")||operator.equals("==")||operator.equals("+=")
                ||operator.equals("-=")||operator.equals("/=")||operator.equals("*=")
               || operator.equals("<=")||operator.equals(">=")||operator.equals("<")
                ||operator.equals(">")){           //(i==5)
        
           if(leftType.equals("int") && rightType.equals("int-const")){
                return true;
           }
            else if(leftType.equals("float") &&rightType.equals("float-const")){
                return true;
           }
         
           else if(leftType.equals("float") &&rightType.equals("int-const")){
                return true;
           }
            else if(leftType.equals("char") &&rightType.equals("char-const")){
                return true;
           }
         else if(leftType.equals("String") &&rightType.equals("String-const")){
                return true;
           }
            else if(leftType.equals("bool") &&rightType.equals("bool-const")){
                return true;
           }
        
        
        
        }
        
        if(operator.equals("No-check")){ 
          return true;
        }
        
       return false;
    }
    
   
    
    
     
    
   void showData(){
        for (int i = 0; i < clas.size(); i++) {
            System.out.println(clas.get(i).name+" "+clas.get(i).type+" "+clas.get(i).category+" "+clas.get(i).parent);
            //System.out.println("Link of "+clas.get(i).name+"=>"+clas.get(i).Link.CB.name+","+clas.get(i).Link.CB.type);
        }
         
       //System.out.println("Link of "+clas.get(1).name+"=>"+clas.get(1).Link.classbody.get(3).name+" "+clas.get(1).Link.classbody.get(3).type
        //+" "+clas.get(1).Link.classbody.get(3).staticModifier+" "+clas.get(1).Link.classbody.get(3).TypeModifier);
        //System.out.println("Link of "+clas.get(1).name+"=>"+clas.get(1).Link.classbody.get(0).name);
        
        for(int i = 0; i < func.size(); i++){
             System.out.println(func.get(i).name+" "+func.get(i).type+" "+func.get(i).scope+" "+func.get(i).assigned);
        }
      
    }
      
    
}
