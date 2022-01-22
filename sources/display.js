"use strict";

const vs = `#version 300 es

layout(location = 0) in vec3 v_in;

out vec3 t_coords;

uniform float u_time;
uniform float u_point_size;

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

    t_coords = v_in.xyy;

    mat4 V = translate(vec3(0., 0., -2.5))*rotateXZ(u_time*0.);
    mat4 P = project(.01, 10., 1./.5, 1.);

    vec4 pos_out = P*V*p;

    gl_PointSize = u_point_size;
    //gl_Position = vec4(p.xyz, 1.);
    gl_Position = pos_out;
}`;

const fs = `#version 300 es
precision highp float;

layout(location = 0) out vec4 fragColor;

in vec3 t_coords;

uniform vec3 u_color;

void main()
{
    fragColor = vec4(u_color, 1.);
}`;

class display
{
    gl;
    wgl;

    timeline_el;
    timeline_value;

    /*mouse = {
        is_down: false,
        
    };*/

    vbo_vertices;
    shader_prg;
    u_time;
    u_point_size;
    u_color;

    vao_all_vertices = null;
    vao_convex_hull = null;
    vao_list = [];
    
    constructor(canvas_el, timeline_el)
    {
        this.wgl = new wgl(canvas_el);
        this.gl = this.wgl.get_gl();

        this.timeline_el = timeline_el;
        this.timeline_el.disabled = true;
        this.timeline_el.min = -1;
        this.timeline_el.max = 1;
        this.timeline_el.step = 1;
        this.timeline_el.value = this.timeline_value = -1;

        this.init_events();

        let gl = this.gl;
        this.shader_prg = this.wgl.init_shader_program(vs, fs);
        this.u_time = gl.getUniformLocation(this.shader_prg, "u_time");
        this.u_point_size = gl.getUniformLocation(this.shader_prg, "u_point_size");
        this.u_color = gl.getUniformLocation(this.shader_prg, "u_color");
    }

    init_events()
    {
        this.timeline_el.addEventListener("input", () => {
            this.timeline_value = parseInt(this.timeline_el.value);
            this.new_frame();
        });
        this.gl.canvas.addEventListener("mousedown", () => {
            console.log("mouse down");
        });
        this.gl.canvas.addEventListener("mouseup", () => {
            console.log("mouse up");
        });
        this.gl.canvas.addEventListener("mousemove", () => {
            console.log("mouse move");
        });
    }

    init_vertex_list(list)
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

        let min_coord = Math.max(Math.max(min_x, min_y), min_z);
        let max_coord = Math.max(Math.max(max_x, max_y), max_z);
        let diff = max_coord - min_coord;
        diff_x = (diff_x/diff)*.5;
        diff_y = (diff_y/diff)*.5;
        diff_z = (diff_z/diff)*.5;

        const defined_or_zero = (x) => Number.isNaN(x) ? 0 : x;

        let gl = this.gl;
        let new_list = new Array(list.length*3);
        for(let i = 0; i < list.length; i++)
        {
            new_list[i*3] = defined_or_zero((list[i].x - min_x)/diff - diff_x);
            new_list[i*3 + 1] = defined_or_zero((list[i].y - min_y)/diff - diff_y);
            new_list[i*3 + 2] = defined_or_zero((list[i].z - min_z)/diff - diff_z);
        }

        this.vbo_vertices = this.wgl.init_vbo_position(new_list);
        this.vao_all_vertices = this.wgl.new_vao(new_ordered_int_list(list.length), this.vbo_vertices);

        this.vao_list = [];
    }

    push_result_indices(list)
    {
        this.vao_convex_hull = this.wgl.new_vao(list, this.vbo_vertices);
    }

    push_indices(list)
    {
        this.vao_list.push(this.wgl.new_vao(list, this.vbo_vertices));
    }

    set_ready()
    {
        this.timeline_el.max = this.vao_list.length + 1;
        this.timeline_el.disabled = false;
    }

    autoplay()
    {
        this.timeline_el.disabled = true;
        const autoplay_rec = (i) => {
            if(i <= parseInt(this.timeline_el.max))
            {
                window.setTimeout(() => {
                    this.timeline_el.value = this.timeline_value = i;
                    this.new_frame();
                    //this.wgl.capture_frame(1, frame" + "i);
                    autoplay_rec(i + 1);
                }, 100);
            }
            else
            {
                this.timeline_el.disabled = false;
            }
        }
        autoplay_rec(0);
    }

    new_frame()
    {
        let gl = this.gl;

        const loop = () =>
        {
            const time = performance.now()*.001;

            gl.viewport(0, 0, gl.canvas.width, gl.canvas.height);
            gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT);

            gl.useProgram(this.shader_prg);
            gl.uniform1f(this.u_time, time);

            if(this.timeline_value - 1 < this.vao_list.length)
            {
                //for(let i = 0; i < this.vao_list.length; i++)
                for(let i = Math.min(this.timeline_value, this.vao_list.length - 1); i >= 0; i--)
                {
                    //if(i > this.timeline_value) break;
                    const vao = this.vao_list[i];
                    vao.bind();
                    if(i === this.timeline_value)
                    {
                        gl.uniform3f(this.u_color, 1, 1, 1);
                        gl.uniform1f(this.u_point_size, 6);
                        gl.drawElements(gl.POINTS, vao.nb_tri, gl.UNSIGNED_INT, 0);
                        gl.uniform3f(this.u_color, 1, 1, 0);
                    }
                    else gl.uniform3f(this.u_color, 1, 0, 0);
                    gl.drawElements(gl.LINE_LOOP, vao.nb_tri, gl.UNSIGNED_INT, 0);
                }
            }
            else
            {
                this.vao_convex_hull.bind();
                gl.uniform3f(this.u_color, 1, 1, 1);
                gl.uniform1f(this.u_point_size, 5);
                gl.drawElements(gl.POINTS, this.vao_convex_hull.nb_tri, gl.UNSIGNED_INT, 0);
                gl.uniform3f(this.u_color, 0, 1, 0);
                gl.drawElements(gl.LINE_LOOP, this.vao_convex_hull.nb_tri, gl.UNSIGNED_INT, 0);
            }

            gl.uniform3f(this.u_color, 1, 1, 1);
            gl.uniform1f(this.u_point_size, 2);
            this.vao_all_vertices.bind();
            gl.drawElements(gl.POINTS, this.vao_all_vertices.nb_tri, gl.UNSIGNED_INT, 0);

            gl.bindVertexArray(null);
            gl.useProgram(null);

            //window.requestAnimationFrame(loop);
        }
        window.requestAnimationFrame(loop)
    }

}