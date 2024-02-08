#include <iostream>
#include <tgmath.h>
#include <cmath>
#include <vector>
#include <cstring>
#include <climits>
#include <experimental/iterator>#include <memory>

struct LambdaExpr; // forward declaration

using Lambda = shared_ptr<LambdaExpr>;

struct LambdaExpr {
    
    // variable (var)
    string var; // name
    
    // abstraction (assoc)
    string arg; // formal parameter
    Lambda body; // function body
    
    // application (app)
    Lambda left; // callee
    Lambda right; // argument
    
};

Lambda parse_expr(string s, int& i);
Lambda parse(string s);
string lambda_type(Lambda e);
Lambda alpha(Lambda e, string new_arg);


ostream& operator<<(ostream& out, Lambda e) {
    string type = lambda_type(e);
    if (type == "var") {
        out << e->var;
    } else if (type == "assoc") {
        out << "(\\" << e->arg << "." << e->body << ")";
    } else if (type == "app") {
        out << "(" << e->left << " " << e->right << ")";
    } else {
        out << "???";
    }
    return out;
}

bool operator==(Lambda a, Lambda b) {
    if (a != nullptr && b != nullptr) {
        return (
            a->var == b->var && 
            a->arg == b->arg &&
            a->body == b->body &&
            a->left == b->left &&
            a->right == b->right 
        );
    } else if (a == nullptr && b == nullptr) {
        return true;
    } else {
        return false;
    }
}

string remove_spaces(string s) {
    string t = "";
    for (int i = 0; i < s.size(); i++) {
        if (s[i] != ' ') {
            t = t + s[i];
        }
    }
    return t;
}

[[noreturn]]
void syntax_error() {
    throw runtime_error("syntax error");
}

Lambda new_lambda() {
    Lambda res = make_shared<LambdaExpr>();
    res->var = "";
    res->arg = "";
    res->body = nullptr;
    res->left = nullptr;
    res->right = nullptr;
    return res;
}

Lambda parse_part(string s, int& i) {
    if (s[i] == '(') {   // parentherized expression
        i++;
        Lambda e = parse_expr(s, i);
        if (s[i] == ')') {
            i++;
            return e;
        } else {
            syntax_error();
        }
    } else if (s[i] == '\\') {  // abstraction
        i++;  // skip '\'
        Lambda e = new_lambda();
        e->arg = s[i];
        i++;  // skip argument name
        if (s[i] == '.') {
            i++;
            e->body = parse_expr(s, i);
            return e;
        } else {
           syntax_error();
        }
    } else {  // abstraction 
        Lambda e = new_lambda();
        e->var = s[i];
        i++;  // skip over variable name 
        return e;        
    }
}

Lambda parse_expr(string s, int& i) {
    Lambda left = parse_part(s, i);
    while (i < s.size() && s[i] != ')') {
        Lambda right = parse_part(s, i);
        Lambda e = new_lambda();
        e->left = left;
        e->right = right;
        left = e;
    }
    return left;
}

Lambda parse(string s) {
    s = remove_spaces(s);
    int i = 0;
    Lambda e = parse_expr(s, i);
    if (i == s.size()) {
        return e;
    } else {
        syntax_error();
    }
}

string lambda_type(Lambda e) {
    if (e->var != "") {
        return "var";
    } else if (e->arg != "" && e->body) {
        return "assoc";
    } else if (e->left && e->right) {
        return "app";
    } else {
        return "unknown";
    }
}

[[noreturn]] 
void alpha_error() {
    throw runtime_error("can not make alpha-conversion");
}

// finds `name` as free variable in `e`
bool find_reference(Lambda e, string name) {
    string type = lambda_type(e);
    if (type == "var") {
        return e->var == name;
    } else if (type == "app") {
        bool found_left = find_reference(e->left, name);
        bool found_right = find_reference(e->right, name);
        return found_left || found_right;
    } else if (type == "assoc") {
        if (e->arg == name) {
            return false;
        } else {
            return find_reference(e->body, name);    
        }
    } else {
        return false;
    }
}

Lambda rename_references(Lambda e, string old_arg, string new_arg) {
    string type = lambda_type(e);
    if (type == "var") {
        if (e->var == old_arg) {
            Lambda e2 = new_lambda();
            e2->var = new_arg;
            return e2;
        } else if (e->var == new_arg) {
            alpha_error();
        } else { 
            return e;
        }
    } else if (type == "app") {
        Lambda new_left = rename_references(e->left, old_arg, new_arg);
        Lambda new_right = rename_references(e->right, old_arg, new_arg);
        if (new_left != e->left || new_right != e->right) {
            Lambda e2 = new_lambda();
            e2->left = new_left;
            e2->right = new_right;
            return e2;
        } else {
            return e;
        }
    } else if (type == "assoc") {
        if (e->arg == old_arg) {
            if (find_reference(e->body, new_arg)) {
                alpha_error();
            }
            return e;
        } else if (e->arg == new_arg) {
            if (find_reference(e->body, old_arg)) {
                alpha_error();
            } 
            return e;
        } else {
            Lambda new_body = rename_references(e->body, old_arg, new_arg);
            if (new_body != e->body) {
                Lambda e2 = new_lambda();
                e2->arg = e->arg;
                e2->body = new_body;
                return e2;
            } else {
                return e;
            }
        }         
    } else {
        alpha_error();
    }
}

Lambda alpha(Lambda e, string new_arg) {
    if (lambda_type(e) == "assoc") {
        Lambda e2 = new_lambda();
        e2->arg = new_arg;
        e2->body = rename_references(e->body, e->arg, e2->arg);
        return e2;
    } else {
        alpha_error();
    }
}

[[noreturn]] 
void beta_error() {
    throw runtime_error("can not apply beta-reduction");
}               

/*
x[x := N] = N
y[x := N] = y, if x ≠ y
(M1 M2)[x := N] = M1[x := N] M2[x := N]
(λx.M)[x := N] = λx.M
(λy.M)[x := N] = λy.(M[x := N]), if x ≠ y and y ∉ FV(N)
*/
Lambda substitute(Lambda e, string arg, Lambda value) {
    string type = lambda_type(e);
    if (type == "var") {
        if (e->var == arg) {
            return value;
        } else {
            return e;
        }
    } else if (type == "assoc") {
        if (e->arg == arg) {
            return e;
        } else {
            Lambda new_body = substitute(e->body, arg, value);            
            if (new_body != e->body) {
                if (find_reference(value, e->arg)) {
                    beta_error();  // name conflict
                } else {
                    Lambda e2 = new_lambda();
                    e2->arg = e->arg;
                    e2->body = new_body;
                    return e2;
                }
            } else {
                return e;
            }
        }
    } else if (type == "app") {
        Lambda new_left = substitute(e->left, arg, value);
        Lambda new_right = substitute(e->right, arg, value);
        if (new_left != e->left || new_right != e->right) {
            Lambda e2 = new_lambda();
            e2->left = new_left;
            e2->right = new_right;
            return e2;
        } else {
            return e;
        }
    } else {
        beta_error();
    }
}

Lambda beta(Lambda e) {
    if (lambda_type(e) == "app") {
        if (lambda_type(e->left) == "assoc") {
            Lambda func = e->left;
            Lambda value = e->right;
            return substitute(func->body, func->arg, value);
        } else {
            return e;
        }
    } else {
        return e;        
    }
}        

int main() {
    cout << boolalpha;
    //cout << (alpha(parse("\\x. \\y.xy "), "z") == parse("\\z. \\y.zy ")) << endl;
    //cout << (alpha(parse("\\x.\\x.xx"), "z") == parse("\\z.\\x.xx")) << endl;   
    //cout << (alpha(parse("x"), "z")) << endl;// == parse("\\z.\\x.xx")) << endl;   
    //cout << (alpha(parse("\\x.\\x.z"), "z") == parse("\\z.\\x.xx")) << endl;   
    
    //Lambda e = parse("\\x.\\y.yx");
    //cout << e << endl;

    //cout << parse("\\x.y") << endl;
    //cout << (parse("\\x.yx")) << endl;
    //cout << (parse("(\\x.y)z")) << endl;
    //cout << (parse("z")) << endl;
    //      
    //cout << (parse("y")) << endl;
    //cout << (parse("f x")) << endl;
    //cout << (parse("fx")) << endl;
    //cout << (parse("((f)) ((x))")) << endl;
    //cout << (parse("abcd")) << endl;
    //cout << (parse("((a b) c) d")) << endl;
    //cout << (parse("\\x . x")) << endl;
    //cout << (parse("(\\x . x) y")) << endl;
    //cout << (parse("a b")) << endl;
    //cout << (parse("\\x . (x y)")) << endl;
    //cout << (parse("(\\x.y) \\z.w")) << endl;

    return 0;
}


