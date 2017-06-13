NOTES:
  - types and values use different namespaces
  - a specific token shall be between ``
  - the special token empty shall be the absence of a token

file :=
  item-definition*

item-definition :=
  | # type-definition
  | value-definition
  | # using-declaration

type-definition :=
  `type` identifier `::` type-definition-kind

value-definition :=
  identifier `::` value-definition-kind

value-definition-kind :=
  fn-definition

fn-definition := `fn` `(` `)` opt-return-type block

opt-return-type :=
  | empty
  | `->` type

type :=
  | identifier
  | tuple

tuple :=
  | `(` `)`

block :=
  `{` statement* expression `}`

statement :=
  | expression `;`

expression :=
  | number-literal
  | empty
