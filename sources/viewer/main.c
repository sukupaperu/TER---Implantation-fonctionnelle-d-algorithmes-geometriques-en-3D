#include <GL/glut.h>
#include <GL/glx.h>
#include <stdlib.h>
#include <stdio.h>
#include <math.h>

#define WHITE \
	(Color) { 1, 1, 1 }
#define BLUE \
	(Color) { 49.f / 255, 89.f / 255, 201.f / 255 }
#define GREEN \
	(Color) { 89.f / 255, 201.f / 255, 49.f / 255 }
#define RED \
	(Color) { 201.f / 255, 49.f / 255, 89.f / 255 }
#define GREY \
	(Color) { .5, .5, .5 }

#define VERTICES_COLOR WHITE
#define VERTICES_HULL_COLOR GREEN
#define OUTSIDE_FACE_COLOR BLUE
#define INSIDE_FACE_COLOR GREY

/*******************STRUCTURES********************/
typedef struct
{
	GLdouble r, g, b;
} Color;

typedef struct
{
	float x, y, z;
} Vec3;

typedef struct
{
	Vec3 *list;
	uint size;
} Vec3List;

typedef struct
{
	uint a, b, c;
} Face;

typedef struct
{
	Face *list;
	uint size;
} FaceList;

typedef enum
{
	LEFT_PRESSED,
	LEFT_RELEASED
} MouseState;

/*******************MISC********************/
uint maxInt(int a, int b)
{
	return a > b ? a : b;
}

uint minInt(int a, int b)
{
	return a < b ? a : b;
}

float minFloat(float a, float b)
{
	return a < b ? a : b;
}

float maxFloat(float a, float b)
{
	return a > b ? a : b;
}

Vec3 cross(Vec3 a, Vec3 b)
{
	return (Vec3){
		a.y * b.z - a.z * b.y,
		a.z * b.x - a.x * b.z,
		a.x * b.y - a.y * b.x};
}
Vec3 mult(Vec3 a, Vec3 b)
{
	return (Vec3){a.x * b.x, a.y * b.y, a.z * b.z};
}
Vec3 multf(Vec3 a, float b)
{
	return (Vec3){a.x * b, a.y * b, a.z * b};
}
Vec3 add(Vec3 a, Vec3 b)
{
	return (Vec3){a.x + b.x, a.y + b.y, a.z + b.z};
}
Vec3 addf(Vec3 a, float b)
{
	return (Vec3){a.x + b, a.y + b, a.z + b};
}
Vec3 sub(Vec3 a, Vec3 b)
{
	return (Vec3){a.x - b.x, a.y - b.y, a.z - b.z};
}
Vec3 subf(Vec3 a, float b)
{
	return (Vec3){a.x - b, a.y - b, a.z - b};
}
Vec3 di(Vec3 a, Vec3 b)
{
	return (Vec3){a.x / b.x, a.y / b.y, a.z / b.z};
}
Vec3 dif(Vec3 a, float b)
{
	return (Vec3){a.x / b, a.y / b, a.z / b};
}
float length(Vec3 a)
{
	return sqrt(a.x * a.x + a.y * a.y + a.z * a.z);
}
Vec3 normalize(Vec3 a)
{
	float l = length(a);
	return (Vec3){a.x / l, a.y / l, a.z / l};
}

/*******************FILE OPERATIONS********************/
void openFile(FILE **file, char *fileName)
{
	*file = fopen(fileName, "r");
	if (*file == NULL)
	{
		printf("Error opening file %s\n", fileName);
		exit(-1);
	}
}

uint getNumberOfLines(FILE *f)
{
	uint nb = 0;
	char c;
	while ((c = fgetc(f)) != EOF)
	{
		if (c == '\n')
			nb++;
	}
	rewind(f);
	return nb;
}

void readVec3ListFile(char *fileName, Vec3List *vl)
{
	FILE *file = NULL;
	openFile(&file, fileName);

	int nbVert = getNumberOfLines(file);
	vl->list = (Vec3 *)malloc(sizeof(Vec3) * nbVert);
	vl->size = nbVert;
	for (int i = 0; i < nbVert; i++)
	{
		fscanf(file, "%f %f %f", &vl->list[i].x, &vl->list[i].y, &vl->list[i].z);
	}

	fclose(file);
}

void printVec3List(Vec3List *vl)
{
	for (int i = 0; i < vl->size; i++)
	{
		printf("%f %f %f\n", vl->list[i].x, vl->list[i].y, vl->list[i].z);
	}
}

void readFaceListFile(char *fileName, FaceList *fl, Vec3List *vl)
{
	FILE *file = NULL;
	openFile(&file, fileName);

	uint nbFaces = getNumberOfLines(file);
	if (nbFaces % 3 != 0)
	{
		printf("Error: number of vertex index in %s is not a multiple of 3\n", fileName);
		exit(-1);
	}
	else
	{
		nbFaces /= 3;
	}

	uint maxVertexIndex = vl->size;

	fl->list = (Face *)malloc(sizeof(Face) * nbFaces);
	fl->size = nbFaces;
	for (int i = 0; i < nbFaces; i++)
	{
		uint a, b, c;
		fscanf(file, "%d %d %d", &a, &b, &c);
		int maxIndex = maxInt(a, maxInt(b, c));
		int minIndex = minInt(a, minInt(b, c));
		if (maxIndex >= maxVertexIndex)
		{
			printf("Error: face %d has a vertex index greater (%d) than the number of vertices (%d).\n", i, maxIndex, maxVertexIndex);
			exit(-1);
		}
		else if (minIndex < 0)
		{
			printf("Error: face %d has a vertex index (%d) lower than 0.\n", i, minIndex);
			exit(-1);
		}
		else
		{
			fl->list[i] = (Face){a, b, c};
		}
	}

	fclose(file);
}

void printFaceList(FaceList *fl)
{
	for (int i = 0; i < fl->size; i++)
	{
		printf("%d %d %d\n", fl->list[i].a, fl->list[i].b, fl->list[i].c);
	}
}

/*******************VERTICES OPERATIONS********************/
void minMaxXYZ(Vec3List *vl, float *minX, float *minY, float *minZ, float *maxX, float *maxY, float *maxZ)
{
	*minX = vl->list[0].x;
	*minY = vl->list[0].y;
	*minZ = vl->list[0].z;
	*maxX = vl->list[0].x;
	*maxY = vl->list[0].y;
	*maxZ = vl->list[0].z;

	for (int i = 1; i < vl->size; i++)
	{
		*minX = minFloat(*minX, vl->list[i].x);
		*minY = minFloat(*minY, vl->list[i].y);
		*minZ = minFloat(*minZ, vl->list[i].z);
		*maxX = maxFloat(*maxX, vl->list[i].x);
		*maxY = maxFloat(*maxY, vl->list[i].y);
		*maxZ = maxFloat(*maxZ, vl->list[i].z);
	}
}

void normalizeAndCentralizeVec3List(Vec3List *vl)
{
	float minX, minY, minZ, maxX, maxY, maxZ;
	minMaxXYZ(vl, &minX, &minY, &minZ, &maxX, &maxY, &maxZ);
	float centerX = (maxX + minX) / 2, centerY = (maxY + minY) / 2, centerZ = (maxZ + minZ) / 2;
	float sizeMax = maxFloat(maxX - minX, maxFloat(maxY - minY, maxZ - minZ)) / 2;
	for (int i = 0; i < vl->size; i++)
	{
		vl->list[i].x -= centerX;
		vl->list[i].y -= centerY;
		vl->list[i].z -= centerZ;
		vl->list[i].x /= sizeMax;
		vl->list[i].y /= sizeMax;
		vl->list[i].z /= sizeMax;
	}
}

/*******************DRAWING********************/
void chooseColor(Color c)
{
	glColor3d(c.r, c.g, c.b);
}

void drawPoint(Vec3 p, float size)
{
	glPointSize(size);
	glBegin(GL_POINTS);
	glVertex3d(p.x, p.y, p.z);
	glEnd();
}

void drawLine(Vec3 p1, Vec3 p2)
{
	glBegin(GL_LINES);
	glVertex3d(p1.x, p1.y, p1.z);
	glVertex3d(p2.x, p2.y, p2.z);
	glEnd();
}

void applyNormal(Vec3 p1, Vec3 p2, Vec3 p3)
{
	Vec3 n = normalize(cross(sub(p2, p1), sub(p3, p1)));
	glNormal3d(n.x, n.y, n.z);
}

void drawTriFilled(Vec3 p1, Vec3 p2, Vec3 p3, Color outsideColor, Color insideColor)
{
	glEnable(GL_LIGHTING);
	applyNormal(p1, p2, p3);
	glPolygonMode(GL_FRONT_AND_BACK, GL_FILL);
	chooseColor(outsideColor);
	glBegin(GL_TRIANGLES);
	glVertex3f(p1.x, p1.y, p1.z);
	glVertex3f(p2.x, p2.y, p2.z);
	glVertex3f(p3.x, p3.y, p3.z);
	glEnd();
	chooseColor(insideColor);
	glBegin(GL_TRIANGLES);
	glVertex3f(p3.x, p3.y, p3.z);
	glVertex3f(p2.x, p2.y, p2.z);
	glVertex3f(p1.x, p1.y, p1.z);
	glEnd();
	glDisable(GL_LIGHTING);
}

void drawTriOutlined(Vec3 p1, Vec3 p2, Vec3 p3, Color outsideColor, Color insideColor, float lineWidth)
{
	chooseColor(outsideColor);
	glLineWidth(lineWidth);
	glPolygonMode(GL_FRONT_AND_BACK, GL_LINE);
	glBegin(GL_TRIANGLES);
	glVertex3f(p1.x, p1.y, p1.z);
	glVertex3f(p2.x, p2.y, p2.z);
	glVertex3f(p3.x, p3.y, p3.z);
	glEnd();
	chooseColor(insideColor);
	glLineWidth(1);
	glBegin(GL_TRIANGLES);
	glVertex3f(p3.x, p3.y, p3.z);
	glVertex3f(p2.x, p2.y, p2.z);
	glVertex3f(p1.x, p1.y, p1.z);
	glEnd();
}

void drawHelper(float lineWidth)
{
	glLineWidth(lineWidth);
	chooseColor(RED);
	drawLine((Vec3){-1, 0, 0}, (Vec3){1, 0, 0});
	chooseColor(GREEN);
	drawLine((Vec3){0, -1, 0}, (Vec3){0, 1, 0});
	chooseColor(BLUE);
	drawLine((Vec3){0, 0, -1}, (Vec3){0, 0, 1});
}

void drawPointVec3List(Vec3List *vl, Color pointColor, float pointSize)
{
	chooseColor(pointColor);
	glPointSize(pointSize);
	glBegin(GL_POINTS);
	for (int i = 0; i < vl->size; i++)
	{
		glVertex3d(vl->list[i].x, vl->list[i].y, vl->list[i].z);
	}
	glEnd();
}

void drawTriFaceList(
	Vec3List *vl,
	FaceList *fl,
	Color outsideColor, Color insideColor,
	Color pointColor, float pointSize,
	Color lineColor, float lineWidth,
	int mode)
{
	switch (mode)
	{
	case 0:
	case 1:
		for (int i = 0; i < fl->size; i++)
		{
			drawTriFilled(vl->list[fl->list[i].a], vl->list[fl->list[i].b], vl->list[fl->list[i].c], outsideColor, insideColor);
		}
	case 2:
		if (mode != 0)
		{
			for (int i = 0; i < fl->size; i++)
			{
				drawTriOutlined(vl->list[fl->list[i].a], vl->list[fl->list[i].b], vl->list[fl->list[i].c], lineColor, insideColor, lineWidth);
			}
		}
	case 3:
		chooseColor(pointColor);
		for (int i = 0; i < fl->size; i++)
		{
			drawPoint(vl->list[fl->list[i].a], pointSize);
			drawPoint(vl->list[fl->list[i].b], pointSize);
			drawPoint(vl->list[fl->list[i].c], pointSize);
		}
		break;
	}
}

/*******************DISPLAY********************/
int WIN_WIDTH = 400, WIN_HEIGHT = 400;
double Y_ANGLE = 0, Y_ANGLE_TEMP = 0, ZOOM = -2.25;
int DRAW_MODE = 0;
Vec3List VERTICES;
FaceList FACES;

void initDisplay()
{
	glEnable(GL_CULL_FACE);
	glEnable(GL_DEPTH);
	glEnable(GL_DEPTH_TEST);
	glClearColor(.015, .015, .015, 1.0);

	glEnable(GL_MULTISAMPLE);

	glEnable(GL_FOG);
	glFogfv(GL_FOG_DENSITY, (GLfloat[]){.35});
	glFogfv(GL_FOG_MODE, (GLfloat[]){GL_EXP2});

	glEnable(GL_LIGHT0);
	glEnable(GL_COLOR_MATERIAL);
	glColorMaterial(GL_FRONT_AND_BACK, GL_AMBIENT_AND_DIFFUSE);
}

void display()
{
	glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);

	glMatrixMode(GL_PROJECTION);
	glLoadIdentity();
	gluPerspective(70, (float)WIN_WIDTH / WIN_HEIGHT, 1, 100);

	glMatrixMode(GL_MODELVIEW);
	glLoadIdentity();

	glTranslatef(0, 0, ZOOM);
	glRotated(Y_ANGLE + Y_ANGLE_TEMP, 0, 1, 0);

	drawHelper(1);
	drawTriFaceList(&VERTICES, &FACES, BLUE, GREY, RED, 6, WHITE, 1, DRAW_MODE);
	drawPointVec3List(&VERTICES, WHITE, 1);

	glutSwapBuffers();
}

/*******************EVENTS********************/
void onResize(int w, int h)
{
	WIN_WIDTH = w;
	WIN_HEIGHT = h;
	glViewport(0, 0, w, h);
	glMatrixMode(GL_PROJECTION);
	glLoadIdentity();
}

void keyboard(unsigned char keycode, int x, int y)
{
	switch (keycode)
	{
	case ' ':
		DRAW_MODE = (DRAW_MODE + 1) % 5;
		glutPostRedisplay();
		break;
	}
}

MouseState MOUSE_STATE = LEFT_RELEASED;
float X_MOUSE_WHEN_PRESSED = 0;

void mouse(int button, int state, int x, int y)
{
	if (button == GLUT_LEFT_BUTTON)
	{
		float mX = (float)x / WIN_WIDTH, mY = (float)y / WIN_HEIGHT;
		switch (state)
		{
		case GLUT_DOWN:
			MOUSE_STATE = LEFT_PRESSED;
			X_MOUSE_WHEN_PRESSED = mX;
			break;
		case GLUT_UP:
			MOUSE_STATE = LEFT_RELEASED;
			Y_ANGLE += Y_ANGLE_TEMP;
			Y_ANGLE_TEMP = 0;
			break;
		}
		glutPostRedisplay();
	}
	else if (button == 3)
	{
		ZOOM += .1;
		glutPostRedisplay();
	}
	else if (button == 4)
	{
		ZOOM -= .1;
		glutPostRedisplay();
	}
}

void mouseMotion(int x, int y)
{
	if (MOUSE_STATE == LEFT_PRESSED)
	{
		float mX = (float)x / WIN_WIDTH, mY = (float)y / WIN_HEIGHT;
		Y_ANGLE_TEMP = -(X_MOUSE_WHEN_PRESSED - mX) * 360;
		glutPostRedisplay();
	}
}

/*******************MAIN********************/
int main(int argc, char *argv[])
{
	if (argc < 2)
	{
		printf("Usage: %s <vertex_list_file> <faces_list_file>\n", argv[0]);
		return 1;
	}

	readVec3ListFile(argv[1], &VERTICES);
	normalizeAndCentralizeVec3List(&VERTICES);
	// printVec3List(&VERTICES);
	if (argc >= 3)
		readFaceListFile(argv[2], &FACES, &VERTICES);
	else
		FACES = (FaceList){.size = 0, .list = NULL};

	glutInit(&argc, argv);
	glutInitDisplayMode(GLUT_RGBA | GLUT_DOUBLE | GLUT_DEPTH | GLUT_MULTISAMPLE);

	glutInitWindowSize(WIN_WIDTH, WIN_HEIGHT);
	glutInitWindowPosition(
		GLUT_SCREEN_WIDTH / 2 - WIN_WIDTH / 2,
		GLUT_SCREEN_HEIGHT / 2 - WIN_HEIGHT / 2);
	glutCreateWindow("viewer");

	initDisplay();

	glutDisplayFunc(display);
	glutReshapeFunc(onResize);
	glutKeyboardFunc(keyboard);
	// glutSpecialFunc(special);
	glutMouseFunc(mouse);
	glutMotionFunc(mouseMotion);
	glutMainLoop();

	return 0;
}
