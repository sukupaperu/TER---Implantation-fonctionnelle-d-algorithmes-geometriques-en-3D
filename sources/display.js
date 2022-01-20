"use strict";

const vs = `#version 300 es

layout(location = 0) in vec3 v_in;

uniform float u_time;

mat4 project(float n, float f, float e, float a) {
    float fl = f - n;
    return mat4(e, vec4(0.), e/a, vec4(0.), (f + n)/-fl, -1., vec2(0.), -(2.*f*n)/fl, 0.);
}

mat4 translate(vec3 p)
{
    return mat4(1., vec4(0.), 1., vec4(0.), 1., 0., p, 1.);
}

mat4 rotateXZ(float a)
{
    float c = cos(a), s = sin(a);
    return mat4(c, 0., s, vec2(0.), 1., vec2(0.), -s, 0., c, vec4(0.), 1.);
}

void main()
{
    vec4 p = vec4(v_in, 1.);

    mat4 V = translate(vec3(0., 0., -2.))*rotateXZ(u_time);
    mat4 P = project(.01, 10., 1./.5, 1.);

    vec4 pos_out = P*V*p;

    gl_PointSize = 4.;
    //gl_Position = vec4(p.xyz, 1.);
    gl_Position = pos_out;
}`;

const fs = `#version 300 es
precision highp float;

layout(location = 0) out vec4 fragColor;

uniform vec3 u_color;

void main()
{
    fragColor = vec4(u_color, 1.);
}`;

class display
{
    gl;
    wgl;

    vbo_vertices;
    shader_prg;
    u_time;
    u_color;

    vao_all_vertices = null;
    vao_convex_hull = null;
    
    constructor(canvas_el)
    {
        this.wgl = new wgl(canvas_el);
        this.gl = this.wgl.get_gl();

        let gl = this.gl;

        this.shader_prg = this.wgl.init_shader_program(vs, fs);
        this.u_time = gl.getUniformLocation(this.shader_prg, "u_time");
        this.u_color = gl.getUniformLocation(this.shader_prg, "u_color");

    }

    set_vertex_list(list)
    {
        let max_x = vertex_list.reduce((p,q) => p.x > q.x ? p : q).x;
        let min_x = vertex_list.reduce((p,q) => p.x < q.x ? p : q).x;
        let diff_x = max_x - min_x;
        let max_y = vertex_list.reduce((p,q) => p.y > q.y ? p : q).y;
        let min_y = vertex_list.reduce((p,q) => p.y < q.y ? p : q).y;
        let diff_y = max_y - min_y;
        let max_z = vertex_list.reduce((p,q) => p.z > q.z ? p : q).z;
        let min_z = vertex_list.reduce((p,q) => p.z < q.z ? p : q).z;
        let diff_z = max_z - min_z;

        /*let min_coord = Math.max(Math.max(min_x, min_y), min_z);
        let max_coord = Math.max(Math.max(max_x, max_y), max_z);
        let diff = max_coord - min_coord;*/

        const defined_or_zero = (x) => Number.isNaN(x) ? 0 : x;

        let gl = this.gl;
        let new_list = new Array(list.length*3);
        for(let i = 0; i < list.length; i++)
        {
            new_list[i*3] = defined_or_zero((list[i].x - min_x)/diff_x - .5);
            new_list[i*3 + 1] = defined_or_zero((list[i].y - min_y)/diff_y - .5);
            new_list[i*3 + 2] = defined_or_zero((list[i].z - min_z)/diff_z - .5);
        }

        this.vbo_vertices = this.wgl.init_vbo_position(new_list);
        this.vao_all_vertices = this.wgl.new_vao(new_ordered_int_list(list.length), this.vbo_vertices);
    }

    push_convex_hull_indices(list)
    {
        this.vao_convex_hull = this.wgl.new_vao(list, this.vbo_vertices);
    }

    set_draw_ready()
    {
        let gl = this.gl;

        const loop = () =>
        {
            gl.viewport(0, 0, gl.canvas.width, gl.canvas.height);
            gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT);

            gl.useProgram(this.shader_prg);
            gl.uniform1f(this.u_time, performance.now()*.001);
            gl.uniform3f(this.u_color, 1, 1, 1);
            this.vao_all_vertices.bind();
            gl.drawElements(gl.POINTS, this.vao_all_vertices.nb_tri, gl.UNSIGNED_INT, 0);

            this.vao_convex_hull.bind();
            gl.uniform3f(this.u_color, 1, 0, 0);
            gl.drawElements(gl.LINE_LOOP, this.vao_convex_hull.nb_tri, gl.UNSIGNED_INT, 0);

            gl.bindVertexArray(null);
            gl.useProgram(null);

            window.requestAnimationFrame(loop);
        }
        window.requestAnimationFrame(loop)
    }

}