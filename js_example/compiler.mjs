/** @typedef {} Wasm */

/**
 * @typedef {Object} CompilationResult
 * @property {Object[]} instructions
 * @property {Object[]} data
 * @property {string} msg
 **/

/**
 * @param {import("../pkg/web/creator_compiler.d.ts")} wasm
 * @param {string} json_arch
 * @returns {import("../pkg/web/creator_compiler.d.ts").ArchitectureJS}
 **/
export function load(wasm, json_arch) {
    const arch = wasm.ArchitectureJS.from_json(json_arch);
    return arch
}

/**
 * @param {import("../pkg/web/creator_compiler.d.ts").ArchitectureJS} arch
 * @param {string} code
 * @returns {CompilationResult}
 **/
export function compile(arch, code) {
    const compiled = arch.compile(code, typeof document != "undefined");
    const result = {
        instructions: compiled.instructions.map(x => ({
            address: x.address,
            labels: x.labels,
            loaded: x.loaded,
            binary: x.binary,
            user: x.user
        })),
        data: compiled.data,
        msg: `Code compiled successfully\n` + compiled.toString(),
    };
    return result;
}
