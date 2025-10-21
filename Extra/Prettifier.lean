abbrev ESC := "\x1B"
def BLACK (s : String) := s!"{ESC}[30m{s}{ESC}[0m"
def RED (s : String) := s!"{ESC}[91m{s}{ESC}[0m"
def BROWN (s : String) := s!"{ESC}[31m{s}{ESC}[0m"
def GREEN (s : String) := s!"{ESC}[32m{s}{ESC}[0m"
def YELLOW (s : String) := s!"{ESC}[33m{s}{ESC}[0m"
def BLUE (s : String) := s!"{ESC}[34m{s}{ESC}[0m"
def MAGENTA (s : String) := s!"{ESC}[35m{s}{ESC}[0m"
def CYAN (s : String) := s!"{ESC}[36m{s}{ESC}[0m"
def WHITE (s : String) := s!"{ESC}[37m{s}{ESC}[0m"
def BOLD (s : String) := s!"{ESC}[1m{s}{ESC}[0m"
def ITALIC (s : String) := s!"{ESC}[3m{s}{ESC}[0m"
def UNDERLINE (s : String) := s!"{ESC}[4m{s}{ESC}[0m"
def INVERSE (s : String) := s!"{ESC}[7m{s}{ESC}[0m"

def paren (p : Nat -> Bool) (f : Std.Format) (prec : Nat) : Std.Format := bif p prec then .paren f else f
-- def paren' (prec : Nat) (f : Nat -> Std.Format) (prec' : Nat) : Std.Format := paren (· >= prec) (f prec') prec'

universe u
variable {α β : Type u}

def «infixl»  (f : α -> Nat -> Std.Format) (p_op : Nat) (op : String) (x y : α) : Nat -> Std.Format := paren (· > p_op) (f x p_op ++ " " ++ op ++ " " ++ f y (p_op+1))
def «infixr»  (f : α -> Nat -> Std.Format) (p_op : Nat) (op : String) (x y : α) : Nat -> Std.Format := paren (· > p_op) (f x (p_op+1) ++ " " ++ op ++ " " ++ f y p_op)
def «infix»   (f : α -> Nat -> Std.Format) (p_op : Nat) (op : String) (x y : α) : Nat -> Std.Format := paren (· >= p_op) (f x p_op ++ " " ++ op ++ " " ++ f y p_op)
def «prefix»  (f : α -> Nat -> Std.Format) (p_op : Nat) (op : String) (x : α)   : Nat -> Std.Format := paren (· > p_op) (op ++ f x p_op)
def «postfix» (f : α -> Nat -> Std.Format) (p_op : Nat) (op : String) (x : α)   : Nat -> Std.Format := paren (· > p_op) (f x p_op ++ op)

def binder (f : α -> Nat -> Std.Format) (p_op : Nat) (p1 : String) (x : String) (p2 : String) (dom : α) (p3 : String) (pred : α) (p4 : String) : Nat -> Std.Format :=
  paren (· > p_op) (p1 ++ x ++ p2 ++ f dom 0 ++ p3 ++ f pred 0 ++ p4)

def binder' (f : α -> Nat -> Std.Format) (f' : β -> Nat -> Std.Format) (p_op : Nat) (p1 : String) (x : String) (p2 : String) (dom : α) (p3 : String) (pred : β) (p4 : String) : Nat -> Std.Format :=
  paren (· > p_op) (p1 ++ x ++ p2 ++ f dom 0 ++ p3 ++ f' pred 0 ++ p4)

def List.printLines [ToString α] (L : List α) : String := String.intercalate "\n" <| L.map toString

def List.toString' [ToString α] (xs : List α) : String :=
  xs.map toString |>.intersperse "," |>.foldl (· ++ ·) ""
