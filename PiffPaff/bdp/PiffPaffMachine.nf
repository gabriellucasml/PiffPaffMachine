Normalised(
THEORY MagicNumberX IS
  MagicNumber(Machine(PiffPaffMachine))==(3.5)
END
&
THEORY UpperLevelX IS
  First_Level(Machine(PiffPaffMachine))==(Machine(PiffPaffMachine));
  Level(Machine(PiffPaffMachine))==(0)
END
&
THEORY LoadedStructureX IS
  Machine(PiffPaffMachine)
END
&
THEORY ListSeesX IS
  List_Sees(Machine(PiffPaffMachine))==(?)
END
&
THEORY ListUsesX IS
  List_Uses(Machine(PiffPaffMachine))==(?)
END
&
THEORY ListIncludesX IS
  Inherited_List_Includes(Machine(PiffPaffMachine))==(?);
  List_Includes(Machine(PiffPaffMachine))==(?)
END
&
THEORY ListPromotesX IS
  List_Promotes(Machine(PiffPaffMachine))==(?)
END
&
THEORY ListExtendsX IS
  List_Extends(Machine(PiffPaffMachine))==(?)
END
&
THEORY ListVariablesX IS
  External_Context_List_Variables(Machine(PiffPaffMachine))==(?);
  Context_List_Variables(Machine(PiffPaffMachine))==(?);
  Abstract_List_Variables(Machine(PiffPaffMachine))==(?);
  Local_List_Variables(Machine(PiffPaffMachine))==(?);
  List_Variables(Machine(PiffPaffMachine))==(?);
  External_List_Variables(Machine(PiffPaffMachine))==(?)
END
&
THEORY ListVisibleVariablesX IS
  Inherited_List_VisibleVariables(Machine(PiffPaffMachine))==(?);
  Abstract_List_VisibleVariables(Machine(PiffPaffMachine))==(?);
  External_List_VisibleVariables(Machine(PiffPaffMachine))==(?);
  Expanded_List_VisibleVariables(Machine(PiffPaffMachine))==(?);
  List_VisibleVariables(Machine(PiffPaffMachine))==(?);
  Internal_List_VisibleVariables(Machine(PiffPaffMachine))==(?)
END
&
THEORY ListInvariantX IS
  Gluing_Seen_List_Invariant(Machine(PiffPaffMachine))==(btrue);
  Gluing_List_Invariant(Machine(PiffPaffMachine))==(btrue);
  Expanded_List_Invariant(Machine(PiffPaffMachine))==(btrue);
  Abstract_List_Invariant(Machine(PiffPaffMachine))==(btrue);
  Context_List_Invariant(Machine(PiffPaffMachine))==(btrue);
  List_Invariant(Machine(PiffPaffMachine))==(btrue)
END
&
THEORY ListAssertionsX IS
  Expanded_List_Assertions(Machine(PiffPaffMachine))==(btrue);
  Abstract_List_Assertions(Machine(PiffPaffMachine))==(btrue);
  Context_List_Assertions(Machine(PiffPaffMachine))==(btrue);
  List_Assertions(Machine(PiffPaffMachine))==(btrue)
END
&
THEORY ListCoverageX IS
  List_Coverage(Machine(PiffPaffMachine))==(btrue)
END
&
THEORY ListExclusivityX IS
  List_Exclusivity(Machine(PiffPaffMachine))==(btrue)
END
&
THEORY ListInitialisationX IS
  Expanded_List_Initialisation(Machine(PiffPaffMachine))==(skip);
  Context_List_Initialisation(Machine(PiffPaffMachine))==(skip);
  List_Initialisation(Machine(PiffPaffMachine))==(skip)
END
&
THEORY ListParametersX IS
  List_Parameters(Machine(PiffPaffMachine))==(?)
END
&
THEORY ListInstanciatedParametersX END
&
THEORY ListConstraintsX IS
  List_Context_Constraints(Machine(PiffPaffMachine))==(btrue);
  List_Constraints(Machine(PiffPaffMachine))==(btrue)
END
&
THEORY ListOperationsX IS
  Internal_List_Operations(Machine(PiffPaffMachine))==(?);
  List_Operations(Machine(PiffPaffMachine))==(?)
END
&
THEORY ListInputX END
&
THEORY ListOutputX END
&
THEORY ListHeaderX END
&
THEORY ListOperationGuardX END
&
THEORY ListPreconditionX END
&
THEORY ListSubstitutionX END
&
THEORY ListConstantsX IS
  List_Valuable_Constants(Machine(PiffPaffMachine))==(?);
  Inherited_List_Constants(Machine(PiffPaffMachine))==(?);
  List_Constants(Machine(PiffPaffMachine))==(?)
END
&
THEORY ListSetsX IS
  Context_List_Enumerated(Machine(PiffPaffMachine))==(?);
  Context_List_Defered(Machine(PiffPaffMachine))==(?);
  Context_List_Sets(Machine(PiffPaffMachine))==(?);
  List_Valuable_Sets(Machine(PiffPaffMachine))==(?);
  Inherited_List_Enumerated(Machine(PiffPaffMachine))==(?);
  Inherited_List_Defered(Machine(PiffPaffMachine))==(?);
  Inherited_List_Sets(Machine(PiffPaffMachine))==(?);
  List_Enumerated(Machine(PiffPaffMachine))==(?);
  List_Defered(Machine(PiffPaffMachine))==(?);
  List_Sets(Machine(PiffPaffMachine))==(?)
END
&
THEORY ListHiddenConstantsX IS
  Abstract_List_HiddenConstants(Machine(PiffPaffMachine))==(?);
  Expanded_List_HiddenConstants(Machine(PiffPaffMachine))==(?);
  List_HiddenConstants(Machine(PiffPaffMachine))==(?);
  External_List_HiddenConstants(Machine(PiffPaffMachine))==(?)
END
&
THEORY ListPropertiesX IS
  Abstract_List_Properties(Machine(PiffPaffMachine))==(btrue);
  Context_List_Properties(Machine(PiffPaffMachine))==(btrue);
  Inherited_List_Properties(Machine(PiffPaffMachine))==(btrue);
  List_Properties(Machine(PiffPaffMachine))==(btrue)
END
&
THEORY ListSeenInfoX END
&
THEORY ListANYVarX END
&
THEORY ListOfIdsX IS
  List_Of_Ids(Machine(PiffPaffMachine)) == (? | ? | ? | ? | ? | ? | ? | ? | PiffPaffMachine);
  List_Of_HiddenCst_Ids(Machine(PiffPaffMachine)) == (? | ?);
  List_Of_VisibleCst_Ids(Machine(PiffPaffMachine)) == (?);
  List_Of_VisibleVar_Ids(Machine(PiffPaffMachine)) == (? | ?);
  List_Of_Ids_SeenBNU(Machine(PiffPaffMachine)) == (?: ?)
END
&
THEORY TCIntRdX IS
  predB0 == OK;
  extended_sees == KO;
  B0check_tab == KO;
  local_op == OK;
  abstract_constants_visible_in_values == KO;
  project_type == SOFTWARE_TYPE;
  event_b_deadlockfreeness == KO;
  variant_clause_mandatory == KO;
  event_b_coverage == KO;
  event_b_exclusivity == KO;
  genFeasibilityPO == KO
END
)
