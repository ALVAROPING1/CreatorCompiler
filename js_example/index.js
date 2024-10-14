import init, * as wasm from "../pkg/creator_compiler.js";

await init({})

const json_arch = `{
  "arch_conf": [
    {
      "name": "Name",
      "value": "RISC-V (RV32IMFD)"
    },
    {
      "name": "Bits",
      "value": "32"
    },
    {
      "name": "Description",
      "value": "RISC-V is an instruction set architecture (ISA) based on the RISC type and its hardware is free. This architecture was created in 2010 at the University of California, Berkeley."
    },
    {
      "name": "Data Format",
      "value": "big_endian"
    },
    {
      "name": "Memory Alignment",
      "value": "1"
    },
    {
      "name": "Main Function",
      "value": "main"
    },
    {
      "name": "Passing Convention",
      "value": "1"
    },
    {
      "name": "Sensitive Register Name",
      "value": "1"
    }
  ],
  "components": [
    {
      "name": "Integer registers",
      "type": "int_registers",
      "double_precision": false,
      "elements": [
        {
          "name": [
            "x0",
            "zero"
          ],
          "nbits": "32",
          "value": 0,
          "default_value": 0,
          "properties": [
            "read",
            "ignore_write"
          ]
        }
      ]
    }
  ],
  "instructions": [
    {
      "name": "nop",
      "type": "Arithmetic integer",
      "signature_definition": "F0 F1",
      "signature": "nop,INT-Reg",
      "signatureRaw": "nop rd",
      "co": "0110011",
      "cop": "0000000000",
      "nwords": 1,
      "clk_cycles": 1,
      "fields": [
        {
          "name": "nop",
          "type": "co",
          "startbit": 6,
          "stopbit": 0
        },
        {
          "name": "rd",
          "type": "INT-Reg",
          "startbit": 11,
          "stopbit": 7
        }
      ],
      "definition": "rd = rs2 + rs1",
      "separated": [
        false,
        false
      ],
      "help": ""
    }
  ],
  "pseudoinstructions": [
    {
      "name": "beqz",
      "signature_definition": "beqz F0 F1",
      "signature": "beqz,INT-Reg,offset_words",
      "signatureRaw": "beqz reg1 off",
      "help": "",
      "properties": [],
      "nwords": 1,
      "fields": [
        {
          "name": "reg1",
          "type": "INT-Reg"
        },
        {
          "name": "off",
          "type": "offset_words"
        }
      ],
      "definition": "beq reg1 x0 off;"
    }
  ],
  "directives": [
    {
      "name": ".data",
      "action": "data_segment",
      "size": null
    },
    {
      "name": ".text",
      "action": "code_segment",
      "size": null
    },
    {
      "name": ".byte",
      "action": "byte",
      "size": "1"
    }
  ],
  "memory_layout": [
    {
      "name": "text start",
      "value": "0x00000000"
    },
    {
      "name": "text end",
      "value": "0x001FFFFF"
    },
    {
      "name": "data start",
      "value": "0x00200000"
    },
    {
      "name": "data end",
      "value": "0x05BBFCBF"
    },
    {
      "name": "stack start",
      "value": "0x0FFFFFFC"
    },
    {
      "name": "stack end",
      "value": "0x0FFFFFFF"
    }
  ]
}`

const arch = wasm.ArchitectureJS.from_json(json_arch);
console.log(arch.toString())
window["arch"] = arch

try {
  const compiled = arch.compile(`
    .data
    label: .byte 1
    .text
    main: nop x0
  `);
  console.log(compiled)
  // copy instruction data out of the wasm memory
  const instructions = compiled.instructions.map(x => ({
    address: x.address,
    labels: x.labels,
    loaded: x.loaded,
    binary: x.binary,
    user: x.user
  }));
  const data = compiled.data
  console.log(instructions)
  console.log(data)
  window["instructions"] = instructions
  window["data"] = data
} catch (e) {
  console.error(e)
}
