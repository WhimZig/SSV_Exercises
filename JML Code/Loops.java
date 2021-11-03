public class Loops {

	// From "Formal Verification with KeY: A Tutorial"
	// Bernhard Beckert, Reiner Hähnle, Martin Hentschel, Peter H. Schmitt
	//@ public normal_behavior
	//@ ensures (\forall int x; 0<=x && x<a.length; a[x]==0);
	public static void fill_zero(int[] a) {
		int k = 0;
		//@ assignable a[*];
		//@ maintaining 0 <= k && k <= a.length; 
		//@ maintaining (\forall int i; 0<=i && i<k; a[i]==0);
		//@ decreasing a.length-k;
		while (k != a.length) {
			a[k] = 0;
			k++;
		}
	}


 	//@ ensures \result == (\forall int i; 0<=i && i<a.length; a[i]==0);
	public static boolean all_zero(int[] a) {
		int n = a.length;
		boolean r=true;
		int k=0;
		//@ maintaining r == (\forall int i; 0<=i && i<k; a[i]==0);
		//@ maintaining k>=0;
		//@ maintaining k<=n;
		//@ decreasing n-k;
		while (k!=n) {
			if (a[k]!=0) { r=false; }
			k=k+1;
		}
		return r;
	}

 	//@ normal_behavior
 	//@ ensures \result == (\num_of int i; 0<=i && i<a.length; a[i]==0);
	public static int count_zero (int[] a) {
		int r=0;
		int k=0;
		//@ maintaining r == (\num_of int i; 0<=i && i<k; a[i]==0);
		//@ maintaining k>=0;
		//@ maintaining k<=a.length;
		//@ decreasing a.length-k;
		while (k!=a.length) {
			if (a[k]!=0) { r=r+1; }
			k=k+1;
		}
		return r;
	}

}
