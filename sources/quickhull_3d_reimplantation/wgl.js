"use strict";

class wgl
{

    gl;

    constructor(canvas_el)
    {
        this.init_wgl(canvas_el);
    }

    get_gl()
    {
        return this.gl;
    }

    init_wgl(c)
    {
        const gl = c.getContext("webgl2", { preserveDrawingBuffer: true });
        if(!gl) alert("WebGL n'est pas compatible avec ce navigateur.");
        gl.clearColor(.05, .05, .05, 1.);
        gl.enable(gl.DEPTH_TEST);
        gl.enable(gl.BLEND); gl.blendFunc(gl.SRC_ALPHA, gl.ONE_MINUS_SRC_ALPHA);
        //this.gl.enable(this.gl.CULL_FACE);
        //this.gl.cullFace(this.gl.FRONT);
        this.gl = gl;
    }

    canvas_size()
    {
        return this.gl.canvas.width;
    };

    prepare_shader(type, src, info)
    {
        const gl = this.get_gl();
        let shader = gl.createShader(type);
        gl.shaderSource(shader, src);
        gl.compileShader(shader);
        gl.flush();
        if(gl.getShaderParameter(shader, gl.COMPILE_STATUS)) return shader;
        console.error(info, "non compilé.");
        console.error(gl.getShaderInfoLog(shader))
        console.log(src);
        gl.deleteShader(shader);
        return null;
    }

    init_shader_program(vs_src, fs_src)
    {
        const gl = this.get_gl();
        let vs = this.prepare_shader(gl.VERTEX_SHADER, vs_src, "Vertex Shader");
        let fs = this.prepare_shader(gl.FRAGMENT_SHADER, fs_src, "Fragment Shader");
        let prg = gl.createProgram();
        gl.attachShader(prg, vs);
        gl.attachShader(prg, fs);
        gl.flush();
        gl.linkProgram(prg);
        if (gl.getProgramParameter(prg, gl.LINK_STATUS)) return prg;
        console.error(gl.getProgramInfoLog(prg));
        gl.deleteProgram(prg);
        return null;
    }

    init_vbo_position(list)
    {
        let vbo_vertices = this.gl.createBuffer();

        this.gl.bindBuffer(this.gl.ARRAY_BUFFER, vbo_vertices); 
        this.gl.bufferData(this.gl.ARRAY_BUFFER, new Float32Array(list), this.gl.STATIC_DRAW);
        this.gl.bindBuffer(this.gl.ARRAY_BUFFER, null);

        return vbo_vertices;
    }

    new_vao(index_list, vbo_vertices)
    {
        const gl = this.get_gl();

        let vbo_indices = gl.createBuffer();
        gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, vbo_indices);
        gl.bufferData(gl.ELEMENT_ARRAY_BUFFER, new Uint32Array(index_list), gl.STATIC_DRAW);

        let vao = gl.createVertexArray();
        gl.bindVertexArray(vao);

        gl.bindBuffer(gl.ARRAY_BUFFER, vbo_vertices);
        gl.vertexAttribPointer(0, 3, gl.FLOAT, false, 0, 0);
        gl.enableVertexAttribArray(0);

        gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, vbo_indices);

        gl.bindVertexArray(null);
        gl.bindBuffer(gl.ARRAY_BUFFER, null);

        return {
            nb_tri: index_list.length,
            bind: () => {
                gl.bindVertexArray(vao);
            }
        };
    }

    new_repere(size)
    {
        const gl = this.get_gl();

        let vbo_vertices = this.init_vbo_position([
            -size, 0, 0, size, 0, 0,
            0, -size, 0, 0, size, 0,
            0, 0, -size, 0, 0, size
        ]);

        let vbo_indices = gl.createBuffer();
        gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, vbo_indices);
        gl.bufferData(gl.ELEMENT_ARRAY_BUFFER, new Uint32Array([
            0, 1, 2, 3, 4, 5
        ]), gl.STATIC_DRAW);

        let vao = gl.createVertexArray();
        gl.bindVertexArray(vao);

        gl.bindBuffer(gl.ARRAY_BUFFER, vbo_vertices);
        gl.vertexAttribPointer(0, 3, gl.FLOAT, false, 0, 0);
        gl.enableVertexAttribArray(0);

        gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, vbo_indices);

        gl.bindVertexArray(null);
        gl.bindBuffer(gl.ARRAY_BUFFER, null);

        return {
            draw: (u_color) => {
                gl.bindVertexArray(vao);
                gl.uniform3f(u_color, 1, .5, .5);
                gl.drawElements(gl.LINES, 2, gl.UNSIGNED_INT, 0);
                gl.uniform3f(u_color, .5, 1, .5);
                gl.drawElements(gl.LINES, 2, gl.UNSIGNED_INT, 4*2);
                gl.uniform3f(u_color, .5, .5, 1);
                gl.drawElements(gl.LINES, 2, gl.UNSIGNED_INT, 4*4);
            }
        };
    }

    capture_frame(quality, title) {
		let imgData = this.gl.canvas.toDataURL('image/png', quality);
		let a = document.createElement("a");
		a.setAttribute("href", imgData);
		a.setAttribute("download", title + ".png");
		a.click();
	}

}