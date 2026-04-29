# HSCSolverHhomogeneousRadialTeukolsky
Code for the computation of the homogeneous solutions of the radial Teukolsky equation. The package includes an integrator that numerically solves the RWZ equation transformed into Hyperboloidal Slicing coordinates. All boundary conditions for the $`R^\text{in}`$ and $`R^\text{up}`$ solutions are implemented. The solver automatically switches to the asymptotic solutions near horizon or $\infty$ for both $`R^\text{in}`$ and $`R^\text{up}`$.


Mathematica files
- ```HSCSolverHomogeneousRadialTeukolsky.wl```: Mathematica package for the calculation of the numerical solutions to the radial Teukolsky equation.
- ```Tutorial.nb```: short tutorial for the package

Installation
The file ```HSCSolverHomogeneousRadialTeukolsky.wl``` must be placed at one of the paths shown in the variables $BaseDirectory (for system-wide installations) and $UserBaseDirectory (for single-user installations). You need to place it in the Applications/ subdirectory (or subfolder) of those returned by those variables. Alternatively, you can load the package using the command

```Get["/absolute_path_where_the_package_is_located/HSCSolverHomogeneousRadialTeukolsky.wl"]; ```


Author:
- Gabriel Andres Piovano
