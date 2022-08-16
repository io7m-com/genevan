/*
 * Copyright © 2022 Mark Raynsford <code@io7m.com> https://www.io7m.com
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR
 * IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 */

package com.io7m.genevan.tests;

import net.jqwik.api.ForAll;
import net.jqwik.api.Property;
import net.jqwik.api.constraints.BigRange;
import org.junit.jupiter.api.Assumptions;

import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.assertTrue;

public class MaxTest
{
  @Property
  public void checkMax(
    @ForAll @BigRange(min = "0") final BigInteger x,
    @ForAll @BigRange(min = "0") final BigInteger y,
    @ForAll @BigRange(min = "0") final BigInteger z)
  {
    final var leBase = x.compareTo(y) <= 0;
    Assumptions.assumeTrue(leBase);

    final var max = y.max(z);
    assertTrue(x.compareTo(max) <= 0, "%s <= %s".formatted(x, max));
  }
}
