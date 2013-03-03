public class Test {

	void test(boolean a) {
		makeFeature(a);
		boolean b = false;
		int x = 0;

		if (a) {
			System.out.println("A");
			b = true;
		}

		if (!b) {
			System.out.println("!A");
			x++;
		}

		System.out.println("done");
	}

	private void makeFeature(boolean a) {
		// TODO Auto-generated method stub

	}

}
