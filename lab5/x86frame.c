#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "table.h"
#include "tree.h"
#include "frame.h"

/*Lab5: Your implementation here.*/

const int F_wordSize = 4;
//varibales
struct F_access_ {
	enum {inFrame, inReg} kind;
	union {
		int offset; //inFrame
		Temp_temp reg; //inReg
	} u;
};

struct F_frame_ {
    Temp_label name;
	F_accessList formals;
	int length;
};

static F_accessList F_AccessList(F_access head, F_accessList tail) {
    F_accessList list = (F_accessList)checked_malloc(sizeof(*list));
    list->head = head;
    list->tail = tail;

    return list;
}


Temp_label F_name(F_frame f){
	return f->name;
}

F_accessList F_formals(F_frame f){
	return f->formals;
}

static F_access InFrame(int offset){
    F_access f_access = (F_access)checked_malloc(sizeof(*f_access));
	f_access->kind = inFrame;
	f_access->u.offset = offset;

	return f_access;
}

static F_access InReg(Temp_temp reg){
    F_access f_access = (F_access)checked_malloc(sizeof(*f_access));
	f_access->kind = inReg;
	f_access->u.reg = reg;

	return f_access;
}

F_frag F_StringFrag(Temp_label label, string str) {   
	F_frag frag = (F_frag)checked_malloc(sizeof(*frag));
	frag->kind = F_stringFrag;
	frag->u.stringg.label = label;
	frag->u.stringg.str = str;

    return frag;                                      
}                                                     
                                                      
F_frag F_ProcFrag(T_stm body, F_frame frame) {   
	F_frag frag = (F_frag)checked_malloc(sizeof(*frag));
	frag->kind = F_procFrag;
	frag->u.proc.body = body;
    frag->u.proc.frame = frame;    

	return frag;                           
}                                                     
                                                      
F_fragList F_FragList(F_frag head, F_fragList tail) { 
	F_fragList fragList = (F_fragList)checked_malloc(sizeof(*fragList));
    fragList->head = head;
	fragList->tail = tail;

	return fragList;                                      
}          

F_frame F_newFrame(Temp_label name, U_boolList formals){
    F_frame frame = (F_frame)checked_malloc(sizeof(*frame));
    F_accessList list = F_AccessList(NULL,NULL), tail = list;
    frame->name = name;
    int count = 0;
	F_access f_access;
	while(formals != NULL){
		bool escape = formals->head;

		if(escape){
			count++;
            f_access = InFrame(count*F_wordSize);
		}
		else{
		    f_access = InReg(Temp_newtemp());
		}
		tail = tail->tail = F_AccessList(f_access,NULL);
		formals = formals->tail;
	}

	F_accessList old = list;
	list = list->tail;
	free(old);

	frame->formals = list;

	return frame; 
}

F_access F_allocLocal(F_frame f, bool escape){
	if(escape){
		F_access f_access = InFrame(-f->length);
		f->length += F_wordSize;
		return f_access;
	}
	else{
		return InReg(Temp_newtemp());
	}
}

Temp_temp F_FP(void) {
    return Temp_newtemp();
}

T_exp F_Exp(F_access f, T_exp framePtr) {
    if (f->kind == inFrame) {
        return T_Mem(T_Binop(T_plus, framePtr, T_Const(f->u.offset)));
    }
    return T_Temp(f->u.reg);
}

T_exp F_externalCall(string s, T_expList args)
{
  return T_Call(T_Name(Temp_namedlabel(s)), args);
}

