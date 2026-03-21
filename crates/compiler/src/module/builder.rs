// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Builder for constructing Move `CompiledModule`s in tests.

use move_binary_format::CompiledModule;
use move_binary_format::file_format::{
    AbilitySet, AddressIdentifierIndex, Bytecode, CodeUnit, Constant, DatatypeHandle,
    DatatypeHandleIndex, DatatypeTyParameter, EnumDefinition, EnumDefinitionIndex, FieldDefinition,
    FieldHandle, FunctionDefinition, FunctionHandle, FunctionHandleIndex, FunctionInstantiation,
    IdentifierIndex, ModuleHandle, ModuleHandleIndex, Signature, SignatureIndex, SignatureToken,
    StructDefInstantiation, StructDefinition, StructDefinitionIndex, StructFieldInformation,
    TypeSignature, VariantDefinition, VariantHandle, VariantJumpTable, Visibility,
};
use move_core_types::account_address::AccountAddress;
use move_core_types::identifier::Identifier;

/// Builder for a Move `CompiledModule` containing functions, structs, and fields.
///
/// Handles all the index bookkeeping (identifiers, signatures, handles)
/// so callers only specify names, types, and bytecode.
pub struct CompiledModuleBuilder {
    address: AccountAddress,
    identifiers: Vec<Identifier>,
    signatures: Vec<Signature>,
    function_handles: Vec<FunctionHandle>,
    function_definitions: Vec<FunctionDefinition>,
    function_instantiations: Vec<FunctionInstantiation>,
    datatype_handles: Vec<DatatypeHandle>,
    struct_defs: Vec<StructDefinition>,
    field_handles: Vec<FieldHandle>,
    struct_def_instantiations: Vec<StructDefInstantiation>,
    constant_pool: Vec<Constant>,
    foreign_modules: Vec<(AccountAddress, IdentifierIndex)>,
    enum_defs: Vec<EnumDefinition>,
    variant_handles: Vec<VariantHandle>,
}

impl Default for CompiledModuleBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl CompiledModuleBuilder {
    /// Create a new module named `"M"` at address `0x0`.
    pub fn new() -> Self {
        Self::named("M", AccountAddress::ZERO)
    }

    /// Create a new module with a custom name and address.
    pub fn named(name: &str, address: AccountAddress) -> Self {
        Self {
            address,
            identifiers: vec![Identifier::new(name).unwrap()],
            signatures: vec![],
            function_handles: vec![],
            function_definitions: vec![],
            function_instantiations: vec![],
            datatype_handles: vec![],
            struct_defs: vec![],
            struct_def_instantiations: vec![],
            field_handles: vec![],
            constant_pool: vec![],
            foreign_modules: vec![],
            enum_defs: vec![],
            variant_handles: vec![],
        }
    }

    /// Add a public function.
    ///
    /// The `FunctionHandleIndex` equals the insertion order (0, 1, …),
    /// which is what `Bytecode::Call(FunctionHandleIndex(n))` needs.
    pub fn function(
        mut self,
        name: &str,
        params: Vec<SignatureToken>,
        returns: Vec<SignatureToken>,
        locals: Vec<SignatureToken>,
        code: Vec<Bytecode>,
    ) -> Self {
        let name_idx = IdentifierIndex(self.identifiers.len() as u16);
        self.identifiers.push(Identifier::new(name).unwrap());

        let params_idx = SignatureIndex(self.signatures.len() as u16);
        self.signatures.push(Signature(params));
        let returns_idx = SignatureIndex(self.signatures.len() as u16);
        self.signatures.push(Signature(returns));
        let locals_idx = SignatureIndex(self.signatures.len() as u16);
        self.signatures.push(Signature(locals));

        let handle_idx = FunctionHandleIndex(self.function_handles.len() as u16);
        self.function_handles.push(FunctionHandle {
            module: ModuleHandleIndex(0),
            name: name_idx,
            parameters: params_idx,
            return_: returns_idx,
            type_parameters: vec![],
        });

        self.function_definitions.push(FunctionDefinition {
            function: handle_idx,
            visibility: Visibility::Public,
            is_entry: false,
            acquires_global_resources: vec![],
            code: Some(CodeUnit {
                locals: locals_idx,
                code,
                jump_tables: vec![],
            }),
        });

        self
    }

    /// Add a public function with jump tables (for `VariantSwitch`).
    pub fn function_with_jump_tables(
        mut self,
        name: &str,
        params: Vec<SignatureToken>,
        returns: Vec<SignatureToken>,
        locals: Vec<SignatureToken>,
        code: Vec<Bytecode>,
        jump_tables: Vec<VariantJumpTable>,
    ) -> Self {
        let name_idx = IdentifierIndex(self.identifiers.len() as u16);
        self.identifiers.push(Identifier::new(name).unwrap());

        let params_idx = SignatureIndex(self.signatures.len() as u16);
        self.signatures.push(Signature(params));
        let returns_idx = SignatureIndex(self.signatures.len() as u16);
        self.signatures.push(Signature(returns));
        let locals_idx = SignatureIndex(self.signatures.len() as u16);
        self.signatures.push(Signature(locals));

        let handle_idx = FunctionHandleIndex(self.function_handles.len() as u16);
        self.function_handles.push(FunctionHandle {
            module: ModuleHandleIndex(0),
            name: name_idx,
            parameters: params_idx,
            return_: returns_idx,
            type_parameters: vec![],
        });

        self.function_definitions.push(FunctionDefinition {
            function: handle_idx,
            visibility: Visibility::Public,
            is_entry: false,
            acquires_global_resources: vec![],
            code: Some(CodeUnit {
                locals: locals_idx,
                code,
                jump_tables,
            }),
        });

        self
    }

    /// Add a native (extern) function declaration — no body.
    pub fn native_function(
        mut self,
        name: &str,
        params: Vec<SignatureToken>,
        returns: Vec<SignatureToken>,
    ) -> Self {
        let name_idx = IdentifierIndex(self.identifiers.len() as u16);
        self.identifiers.push(Identifier::new(name).unwrap());

        let params_idx = SignatureIndex(self.signatures.len() as u16);
        self.signatures.push(Signature(params));
        let returns_idx = SignatureIndex(self.signatures.len() as u16);
        self.signatures.push(Signature(returns));

        let handle_idx = FunctionHandleIndex(self.function_handles.len() as u16);
        self.function_handles.push(FunctionHandle {
            module: ModuleHandleIndex(0),
            name: name_idx,
            parameters: params_idx,
            return_: returns_idx,
            type_parameters: vec![],
        });

        self.function_definitions.push(FunctionDefinition {
            function: handle_idx,
            visibility: Visibility::Public,
            is_entry: false,
            acquires_global_resources: vec![],
            code: None,
        });

        self
    }

    /// Add a generic native (extern) function declaration — no body.
    pub fn generic_native_function(
        mut self,
        name: &str,
        type_params: Vec<AbilitySet>,
        params: Vec<SignatureToken>,
        returns: Vec<SignatureToken>,
    ) -> Self {
        let name_idx = IdentifierIndex(self.identifiers.len() as u16);
        self.identifiers.push(Identifier::new(name).unwrap());

        let params_idx = SignatureIndex(self.signatures.len() as u16);
        self.signatures.push(Signature(params));
        let returns_idx = SignatureIndex(self.signatures.len() as u16);
        self.signatures.push(Signature(returns));

        let handle_idx = FunctionHandleIndex(self.function_handles.len() as u16);
        self.function_handles.push(FunctionHandle {
            module: ModuleHandleIndex(0),
            name: name_idx,
            parameters: params_idx,
            return_: returns_idx,
            type_parameters: type_params,
        });

        self.function_definitions.push(FunctionDefinition {
            function: handle_idx,
            visibility: Visibility::Public,
            is_entry: false,
            acquires_global_resources: vec![],
            code: None,
        });

        self
    }

    /// Add a generic function with type parameters on the handle.
    pub fn generic_function(
        mut self,
        name: &str,
        type_params: Vec<AbilitySet>,
        params: Vec<SignatureToken>,
        returns: Vec<SignatureToken>,
        locals: Vec<SignatureToken>,
        code: Vec<Bytecode>,
    ) -> Self {
        let name_idx = IdentifierIndex(self.identifiers.len() as u16);
        self.identifiers.push(Identifier::new(name).unwrap());

        let params_idx = SignatureIndex(self.signatures.len() as u16);
        self.signatures.push(Signature(params));
        let returns_idx = SignatureIndex(self.signatures.len() as u16);
        self.signatures.push(Signature(returns));
        let locals_idx = SignatureIndex(self.signatures.len() as u16);
        self.signatures.push(Signature(locals));

        let handle_idx = FunctionHandleIndex(self.function_handles.len() as u16);
        self.function_handles.push(FunctionHandle {
            module: ModuleHandleIndex(0),
            name: name_idx,
            parameters: params_idx,
            return_: returns_idx,
            type_parameters: type_params,
        });

        self.function_definitions.push(FunctionDefinition {
            function: handle_idx,
            visibility: Visibility::Public,
            is_entry: false,
            acquires_global_resources: vec![],
            code: Some(CodeUnit {
                locals: locals_idx,
                code,
                jump_tables: vec![],
            }),
        });

        self
    }

    /// Add a function with `acquires` annotations (for global storage ops).
    pub fn function_with_acquires(
        mut self,
        name: &str,
        params: Vec<SignatureToken>,
        returns: Vec<SignatureToken>,
        locals: Vec<SignatureToken>,
        code: Vec<Bytecode>,
        acquires: Vec<StructDefinitionIndex>,
    ) -> Self {
        let name_idx = IdentifierIndex(self.identifiers.len() as u16);
        self.identifiers.push(Identifier::new(name).unwrap());

        let params_idx = SignatureIndex(self.signatures.len() as u16);
        self.signatures.push(Signature(params));
        let returns_idx = SignatureIndex(self.signatures.len() as u16);
        self.signatures.push(Signature(returns));
        let locals_idx = SignatureIndex(self.signatures.len() as u16);
        self.signatures.push(Signature(locals));

        let handle_idx = FunctionHandleIndex(self.function_handles.len() as u16);
        self.function_handles.push(FunctionHandle {
            module: ModuleHandleIndex(0),
            name: name_idx,
            parameters: params_idx,
            return_: returns_idx,
            type_parameters: vec![],
        });

        self.function_definitions.push(FunctionDefinition {
            function: handle_idx,
            visibility: Visibility::Public,
            is_entry: false,
            acquires_global_resources: acquires,
            code: Some(CodeUnit {
                locals: locals_idx,
                code,
                jump_tables: vec![],
            }),
        });

        self
    }

    /// Add a struct definition.
    ///
    /// The `DatatypeHandleIndex` equals the insertion order (0, 1, …).
    /// Reference it with `SignatureToken::Datatype(DatatypeHandleIndex(n))`.
    pub fn struct_definition(
        mut self,
        name: &str,
        abilities: AbilitySet,
        fields: Vec<(&str, SignatureToken)>,
    ) -> Self {
        let name_idx = IdentifierIndex(self.identifiers.len() as u16);
        self.identifiers.push(Identifier::new(name).unwrap());

        let handle_idx = DatatypeHandleIndex(self.datatype_handles.len() as u16);
        self.datatype_handles.push(DatatypeHandle {
            module: ModuleHandleIndex(0),
            name: name_idx,
            abilities,
            type_parameters: vec![],
        });

        let field_defs: Vec<FieldDefinition> = fields
            .into_iter()
            .map(|(field_name, ty)| {
                let field_name_idx = IdentifierIndex(self.identifiers.len() as u16);
                self.identifiers.push(Identifier::new(field_name).unwrap());
                FieldDefinition {
                    name: field_name_idx,
                    signature: TypeSignature(ty),
                }
            })
            .collect();

        self.struct_defs.push(StructDefinition {
            struct_handle: handle_idx,
            field_information: StructFieldInformation::Declared(field_defs),
        });

        self
    }

    /// Add a struct definition with generic type parameters.
    ///
    /// Like `struct_definition` but accepts `DatatypeTyParameter`s, allowing
    /// phantom type parameters (e.g. `struct Balance<phantom T> { value: u64 }`).
    pub fn generic_struct_definition(
        mut self,
        name: &str,
        abilities: AbilitySet,
        type_parameters: Vec<DatatypeTyParameter>,
        fields: Vec<(&str, SignatureToken)>,
    ) -> Self {
        let name_idx = IdentifierIndex(self.identifiers.len() as u16);
        self.identifiers.push(Identifier::new(name).unwrap());

        let handle_idx = DatatypeHandleIndex(self.datatype_handles.len() as u16);
        self.datatype_handles.push(DatatypeHandle {
            module: ModuleHandleIndex(0),
            name: name_idx,
            abilities,
            type_parameters,
        });

        let field_defs: Vec<FieldDefinition> = fields
            .into_iter()
            .map(|(field_name, ty)| {
                let field_name_idx = IdentifierIndex(self.identifiers.len() as u16);
                self.identifiers.push(Identifier::new(field_name).unwrap());
                FieldDefinition {
                    name: field_name_idx,
                    signature: TypeSignature(ty),
                }
            })
            .collect();

        self.struct_defs.push(StructDefinition {
            struct_handle: handle_idx,
            field_information: StructFieldInformation::Declared(field_defs),
        });

        self
    }

    /// Add an enum definition with named variants.
    ///
    /// The `DatatypeHandleIndex` follows the same sequential numbering as structs.
    /// The `EnumDefinitionIndex` equals the insertion order among enums (0, 1, …).
    /// Each variant is `(name, fields)` where fields are `(field_name, type)`.
    pub fn enum_definition(
        mut self,
        name: &str,
        abilities: AbilitySet,
        variants: Vec<(&str, Vec<(&str, SignatureToken)>)>,
    ) -> Self {
        let name_idx = IdentifierIndex(self.identifiers.len() as u16);
        self.identifiers.push(Identifier::new(name).unwrap());

        let handle_idx = DatatypeHandleIndex(self.datatype_handles.len() as u16);
        self.datatype_handles.push(DatatypeHandle {
            module: ModuleHandleIndex(0),
            name: name_idx,
            abilities,
            type_parameters: vec![],
        });

        let variant_defs: Vec<VariantDefinition> = variants
            .into_iter()
            .map(|(variant_name, fields)| {
                let variant_name_idx = IdentifierIndex(self.identifiers.len() as u16);
                self.identifiers.push(Identifier::new(variant_name).unwrap());
                let field_defs = fields
                    .into_iter()
                    .map(|(field_name, ty)| {
                        let field_name_idx = IdentifierIndex(self.identifiers.len() as u16);
                        self.identifiers.push(Identifier::new(field_name).unwrap());
                        FieldDefinition {
                            name: field_name_idx,
                            signature: TypeSignature(ty),
                        }
                    })
                    .collect();
                VariantDefinition {
                    variant_name: variant_name_idx,
                    fields: field_defs,
                }
            })
            .collect();

        self.enum_defs.push(EnumDefinition {
            enum_handle: handle_idx,
            variants: variant_defs,
        });

        self
    }

    /// Add a variant handle (for `PackVariant` / `UnpackVariant` bytecodes).
    ///
    /// The `VariantHandleIndex` equals the insertion order (0, 1, …).
    /// `enum_def` is the index into the enum_defs vector, `variant` is the tag.
    pub fn variant_handle(mut self, enum_def: usize, variant: u16) -> Self {
        self.variant_handles.push(VariantHandle {
            enum_def: EnumDefinitionIndex(enum_def as u16),
            variant,
        });
        self
    }

    /// Add a field handle (for `ImmBorrowField` / `MutBorrowField`).
    ///
    /// The `FieldHandleIndex` equals the insertion order (0, 1, …).
    pub fn field_handle(mut self, owner: StructDefinitionIndex, field: u16) -> Self {
        self.field_handles.push(FieldHandle { owner, field });
        self
    }

    /// Add a function instantiation (for `CallGeneric`).
    ///
    /// The `FunctionInstantiationIndex` equals the insertion order (0, 1, …).
    pub fn function_instantiation(
        mut self,
        handle: FunctionHandleIndex,
        type_args: Vec<SignatureToken>,
    ) -> Self {
        let sig_idx = SignatureIndex(self.signatures.len() as u16);
        self.signatures.push(Signature(type_args));
        self.function_instantiations.push(FunctionInstantiation {
            handle,
            type_parameters: sig_idx,
        });
        self
    }

    /// Add a struct definition instantiation (for `PackGeneric` / `UnpackGeneric`).
    ///
    /// The `StructDefInstantiationIndex` equals the insertion order (0, 1, …).
    pub fn struct_def_instantiation(
        mut self,
        def: StructDefinitionIndex,
        type_args: Vec<SignatureToken>,
    ) -> Self {
        let sig_idx = SignatureIndex(self.signatures.len() as u16);
        self.signatures.push(Signature(type_args));
        self.struct_def_instantiations.push(StructDefInstantiation {
            def,
            type_parameters: sig_idx,
        });
        self
    }

    /// Add a constant to the constant pool.
    ///
    /// The `ConstantPoolIndex` equals the insertion order (0, 1, …).
    pub fn constant(mut self, type_: SignatureToken, data: Vec<u8>) -> Self {
        self.constant_pool.push(Constant { type_, data });
        self
    }

    /// Register a foreign module handle (e.g. a dependency).
    ///
    /// The `ModuleHandleIndex` is `1 + insertion_order` (index 0 is always self).
    /// Returns `(builder, ModuleHandleIndex)`.
    pub fn foreign_module(
        mut self,
        address: AccountAddress,
        name: &str,
    ) -> (Self, ModuleHandleIndex) {
        let name_idx = IdentifierIndex(self.identifiers.len() as u16);
        self.identifiers.push(Identifier::new(name).unwrap());
        let handle_idx = ModuleHandleIndex(1 + self.foreign_modules.len() as u16);
        self.foreign_modules.push((address, name_idx));
        (self, handle_idx)
    }

    /// Add a function handle pointing to a foreign module (no body / no `FunctionDefinition`).
    ///
    /// The `FunctionHandleIndex` follows the same sequential numbering as local functions.
    pub fn foreign_function(
        mut self,
        module: ModuleHandleIndex,
        name: &str,
        params: Vec<SignatureToken>,
        returns: Vec<SignatureToken>,
    ) -> Self {
        let name_idx = IdentifierIndex(self.identifiers.len() as u16);
        self.identifiers.push(Identifier::new(name).unwrap());

        let params_idx = SignatureIndex(self.signatures.len() as u16);
        self.signatures.push(Signature(params));
        let returns_idx = SignatureIndex(self.signatures.len() as u16);
        self.signatures.push(Signature(returns));

        self.function_handles.push(FunctionHandle {
            module,
            name: name_idx,
            parameters: params_idx,
            return_: returns_idx,
            type_parameters: vec![],
        });

        self
    }

    /// Add a raw `Signature` entry (e.g. for `VecXxx` bytecodes).
    ///
    /// Returns `(builder, SignatureIndex)`.
    pub fn signature(mut self, tokens: Vec<SignatureToken>) -> (Self, SignatureIndex) {
        let idx = SignatureIndex(self.signatures.len() as u16);
        self.signatures.push(Signature(tokens));
        (self, idx)
    }

    /// Assemble into a `CompiledModule`.
    pub fn build(self) -> CompiledModule {
        // Deduplicate addresses: self.address first, then foreign addresses
        let mut address_identifiers = vec![self.address];
        let mut addr_index_map = std::collections::HashMap::new();
        addr_index_map.insert(self.address, AddressIdentifierIndex(0));
        for &(addr, _) in &self.foreign_modules {
            let len = address_identifiers.len();
            addr_index_map.entry(addr).or_insert_with(|| {
                address_identifiers.push(addr);
                AddressIdentifierIndex(len as u16)
            });
        }

        // Build module_handles: index 0 = self, then foreign modules
        let mut module_handles = vec![ModuleHandle {
            address: AddressIdentifierIndex(0),
            name: IdentifierIndex(0),
        }];
        for &(addr, name_idx) in &self.foreign_modules {
            module_handles.push(ModuleHandle {
                address: addr_index_map[&addr],
                name: name_idx,
            });
        }

        CompiledModule {
            version: 7,
            publishable: true,
            self_module_handle_idx: ModuleHandleIndex(0),
            module_handles,
            identifiers: self.identifiers,
            address_identifiers,
            function_handles: self.function_handles,
            function_defs: self.function_definitions,
            signatures: self.signatures,
            struct_defs: self.struct_defs,
            datatype_handles: self.datatype_handles,
            constant_pool: self.constant_pool,
            metadata: vec![],
            field_handles: self.field_handles,
            friend_decls: vec![],
            struct_def_instantiations: self.struct_def_instantiations,
            function_instantiations: self.function_instantiations,
            field_instantiations: vec![],
            enum_defs: self.enum_defs,
            enum_def_instantiations: vec![],
            variant_handles: self.variant_handles,
            variant_instantiation_handles: vec![],
        }
    }
}
