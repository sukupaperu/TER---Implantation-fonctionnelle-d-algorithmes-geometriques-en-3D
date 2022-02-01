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
        this.gl = c.getContext("webgl2", { preserveDrawingBuffer: true });
        if(!this.gl) alert("WebGL n'est pas compatible avec ce navigateur.");
        this.gl.clearColor(.05, .05, .05, 1.);
        this.gl.enable(this.gl.DEPTH_TEST);
        //this.gl.enable(this.gl.CULL_FACE);
        //this.gl.cullFace(this.gl.FRONT);
    }

    canvas_size()
    {
        return this.gl.canvas.width;
    };

    prepare_shader(type, src, info)
    {
        let shader = this.gl.createShader(type);
        this.gl.shaderSource(shader, src);
        this.gl.compileShader(shader);
        this.gl.flush();
        if(this.gl.getShaderParameter(shader, this.gl.COMPILE_STATUS)) return shader;
        console.error(info, "non compilé.");
        console.error(this.gl.getShaderInfoLog(shader))
        console.log(src);
        this.gl.deleteShader(shader);
        return null;
    }

    init_shader_program(vs_src, fs_src)
    {
        let vs = this.prepare_shader(this.gl.VERTEX_SHADER, vs_src, "Vertex Shader");
        let fs = this.prepare_shader(this.gl.FRAGMENT_SHADER, fs_src, "Fragment Shader");
        let prg = this.gl.createProgram();
        this.gl.attachShader(prg, vs);
        this.gl.attachShader(prg, fs);
        this.gl.flush();
        this.gl.linkProgram(prg);
        if (this.gl.getProgramParameter(prg, this.gl.LINK_STATUS)) return prg;
        console.error(this.gl.getProgramInfoLog(prg));
        this.gl.deleteProgram(prg);
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
        let vbo_indices = this.gl.createBuffer();
        this.gl.bindBuffer(this.gl.ELEMENT_ARRAY_BUFFER, vbo_indices);
        this.gl.bufferData(this.gl.ELEMENT_ARRAY_BUFFER, new Uint32Array(index_list), this.gl.STATIC_DRAW);

        let vao = this.gl.createVertexArray();
        this.gl.bindVertexArray(vao);

        this.gl.bindBuffer(this.gl.ARRAY_BUFFER, vbo_vertices);
        this.gl.vertexAttribPointer(0, 3, this.gl.FLOAT, false, 0, 0);
        this.gl.enableVertexAttribArray(0);

        this.gl.bindBuffer(this.gl.ELEMENT_ARRAY_BUFFER, vbo_indices);

        this.gl.bindVertexArray(null);
        this.gl.bindBuffer(this.gl.ARRAY_BUFFER, null);

        return {
            nb_tri: index_list.length,
            bind: () => {
                this.gl.bindVertexArray(vao);
            }
        };
    }

    new_repere(size)
    {
        let vbo_vertices = this.init_vbo_position([
            -size, 0, 0, size, 0, 0,
            0, -size, 0, 0, size, 0,
            0, 0, -size, 0, 0, size
        ]);

        let vbo_indices = this.gl.createBuffer();
        this.gl.bindBuffer(this.gl.ELEMENT_ARRAY_BUFFER, vbo_indices);
        this.gl.bufferData(this.gl.ELEMENT_ARRAY_BUFFER, new Uint32Array([
            0, 1, 2, 3, 4, 5
        ]), this.gl.STATIC_DRAW);

        let vao = this.gl.createVertexArray();
        this.gl.bindVertexArray(vao);

        this.gl.bindBuffer(this.gl.ARRAY_BUFFER, vbo_vertices);
        this.gl.vertexAttribPointer(0, 3, this.gl.FLOAT, false, 0, 0);
        this.gl.enableVertexAttribArray(0);

        this.gl.bindBuffer(this.gl.ELEMENT_ARRAY_BUFFER, vbo_indices);

        this.gl.bindVertexArray(null);
        this.gl.bindBuffer(this.gl.ARRAY_BUFFER, null);

        const gl = this.gl;
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