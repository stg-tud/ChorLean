def ANSI_RESET_FONT_COLOR := "\u001B[0m"

inductive Color: Type where
| Black |Red |Green |Yellow |Blue |Purple |Cyan |White

def Color.toAnsiFontCode: Color -> String
| Black   => "\u001B[30m"
| Red     => "\u001B[31m"
| Green   => "\u001B[32m"
| Yellow  => "\u001B[33m"
| Blue    => "\u001B[34m"
| Purple  => "\u001B[35m"
| Cyan    => "\u001B[36m"
| White   => "\u001B[37m"

def Color.toAnsiBackCode: Color -> String
| Black   => "\u001B[40m"
| Red     => "\u001B[41m"
| Green   => "\u001B[42m"
| Yellow  => "\u001B[43m"
| Blue    => "\u001B[44m"
| Purple  => "\u001B[45m"
| Cyan    => "\u001B[46m"
| White   => "\u001B[47m"


def String.dyeFont (s:String) (c:Color): String :=
  s!"{c.toAnsiFontCode}{s}{ANSI_RESET_FONT_COLOR}"

def String.dyeBack (s:String) (c:Color): String :=
  s!"{c.toAnsiBackCode}{s}{Color.Black.toAnsiBackCode}"

def String.dye (s:String) (fc:Color) (bc_opt: Option Color := none): String :=
  (match bc_opt with
  | some bc => (s.dyeBack bc)
  | none => s).dyeFont fc
