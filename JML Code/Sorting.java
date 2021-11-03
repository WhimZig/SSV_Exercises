public class Sorting {

	//@ normal_behavior
	//@ requires a.length > 1;
	//@ ensures (\forall int i; 0 <= i && i+1 < a.length; a[i] <= a[i+1]);
	//@ ensures ( \forall int v; (\num_of int i; 0<=i && i<a.length; a[i]==v) ==  (\num_of int i; 0<=i && i<\old(a).length; \old(a)[i]==v) );
	public static void bubble_sort(int[] a) {
		int n = a.length;
		if (n==0) { return; }
		
		//@ maintaining ( \forall int v; (\num_of int i; 0<=i && i<a.length; a[i]==v) ==  (\num_of int i; 0<=i && i<\old(a).length; \old(a)[i]==v) );
		//@ maintaining (\forall int i; 0 <= i && i+1 < k; a[i] <= a[i+1]);
		//@ maintaining 1<=n;
		//@ maintaining 1<=k && k<=n;
		//@ decreasing n-k;
		//@ assignable a[*];
		for (int k=1; k!=n; ++k) {
			//@ maintaining ( \forall int v; (\num_of int i; 0<=i && i<a.length; a[i]==v) ==  (\num_of int i; 0<=i && i<\old(a).length; \old(a)[i]==v) );
		    //@ maintaining (\forall int i; 0 <= i && i+1 < j; a[i] <= a[i+1]);
		    //@ maintaining (\forall int i; j <= i && i < k; a[i] <= a[i+1]);
		    //@ maintaining (j==0 || j==k) || a[j-1]<=a[j+1];
		    //@ maintaining (\forall int i; 0 <= i && i < k; (i+1==j && (j==k || a[i]<=a[i+2])) || a[i] <= a[i+1]);
		    //@ maintaining 0<=j && j<=k;
			//@ decreasing j;
			//@ assignable a[*];
			for (int j=k; j!=0; --j) {
				if (a[j] < a[j-1]) { 
					//@ assignable a[*];
					int t=a[j]; a[j]=a[j-1]; a[j-1]=t;
				}
			}
		}
		// return a;
	}
	
	// Not provable using OpenJML
	// ensures \forall int i; 0 <= i && i < a.length; (\forall int j; 0 <= j && j < a.length; i<=j ==> a[i] <= a[j]);
	// maintaining \forall int i; 0 <= i && i < k; (\forall int j; 0 <= j && j < k; i<=j ==> a[j] <= a[k]);

	//@ normal_behavior
	//@ ensures \result == (\forall int i; 0 <= i && i+1 < a.length; a[i] <= a[i+1]);
	//@ pure
	public static boolean is_sorted(int[] a) {
		if (a.length==0) { return true; }
		boolean r=true;
		int k=0;
		// assignable r; // MUST go here for JML, or omitted
		//@ maintaining r == (\forall int i; 0 <= i && i < k; a[i] <= a[i+1]);
		//@ maintaining 0<=k && k+1<=a.length;
		//@ decreasing a.length-(k+1);
		//@ assignable r; // MUST go here for Key, but not for JML
		while (k+1!=a.length) {
			if (a[k] > a[k+1]) { r=false; }
			++k;
		}
		return r; 
	}
	
	//@ normal_behavior
	//@ requires is_sorted(a);
	//@ requires (\forall int i; 0 <= i && i < a.length; (\forall int j; 0 <= j && j < a.length; i<=j ==> a[i] <= a[j]));
	//@ requires a.length > 0;
	//@ ensures \result==a[0];
	//@ ensures (\forall int i; 0<=i && i<a.length; \result <= a[i]);
	public static int sorted_minimum_element(int[] a) {
		return a[0];
	}
	
}