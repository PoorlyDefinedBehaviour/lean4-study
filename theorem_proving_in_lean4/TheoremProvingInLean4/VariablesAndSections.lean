def compose (α β γ : Type) (g: β → γ) (f: α → β) (x: α): γ :=
  g (f x)

def doTwice (α : Type) (h : α → α) (x: α) : α :=
  h (h x)

def doThrice (α : Type) (h : α -> α) (x : α) : α :=
  h (h (h x))

-- Same as above
variable (α β γ : Type)

def compose2 (α β γ : Type) (g: β → γ) (f: α → β) (x: α): γ :=
  g (f x)

def doTwice2 (α : Type) (h : α → α) (x: α) : α :=
  h (h x)

def doThrice2 (α : Type) (h : α -> α) (x : α) : α :=
  h (h (h x))

section useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α )

  def compose3 := g (f x)
  def doTwice3 := h (h x)
  def doThrice3 := h (h (h x))
end useful
